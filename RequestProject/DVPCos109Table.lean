import RequestProject.DVPCosSinEval

/-!
# The cosine table at `t = 109` (rung-109)
-/

open Finset

noncomputable section

namespace CriticalLinePhasor.DVP

theorem cos109_br_2 :
    |Real.cos (((109:ℕ):ℝ) * Real.log (2 : ℕ)) - ((988039/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 387047/10000000) (δ := 43/5000000) 109 12
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos109_br_3 :
    |Real.cos (((109:ℕ):ℝ) * Real.log (3 : ℕ)) - ((93297/100000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 460273/5000000) (δ := 189/20000000) 109 19
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos109_br_4 :
    |Real.cos (((109:ℕ):ℝ) * Real.log (4 : ℕ)) - ((238111/250000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 387047/5000000) (δ := 629/100000000) 109 24
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos109_br_5 :
    |Real.cos (((109:ℕ):ℝ) * Real.log (5 : ℕ)) - ((219341/250000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -1251141/10000000) (δ := 981/100000000) 109 28
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos109_br_6 :
    |Real.cos (((109:ℕ):ℝ) * Real.log (6 : ℕ)) - ((433153/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 653797/5000000) (δ := 377/50000000) 109 31
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos109_br_7 :
    |Real.cos (((109:ℕ):ℝ) * Real.log (7 : ℕ)) - ((9337/200000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -952559/2500000) (δ := 577/100000000) 109 34
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos109_br_8 :
    |Real.cos (((109:ℕ):ℝ) * Real.log (8 : ℕ)) - ((178813/200000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 580571/5000000) (δ := 41/6250000) 109 36
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos109_br_9 :
    |Real.cos (((109:ℕ):ℝ) * Real.log (9 : ℕ)) - ((370433/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 1841093/10000000) (δ := 839/100000000) 109 38
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos109_br_10 :
    |Real.cos (((109:ℕ):ℝ) * Real.log (10 : ℕ)) - ((47043/50000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -864093/10000000) (δ := 101/10000000) 109 40
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos109_br_11 :
    |Real.cos (((109:ℕ):ℝ) * Real.log (11 : ℕ)) - ((-81481/100000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -1576999/2500000) (δ := 193/25000000) 109 42
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos109_br_12 :
    |Real.cos (((109:ℕ):ℝ) * Real.log (12 : ℕ)) - ((778919/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 1694641/10000000) (δ := 571/100000000) 109 43
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos109_br_13 :
    |Real.cos (((109:ℕ):ℝ) * Real.log (13 : ℕ)) - ((-124969/125000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 1949579/2500000) (δ := 623/100000000) 109 44
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos109_br_14 :
    |Real.cos (((109:ℕ):ℝ) * Real.log (14 : ℕ)) - ((1251/6250 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -3423189/10000000) (δ := 101/12500000) 109 46
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos109_br_15 :
    |Real.cos (((109:ℕ):ℝ) * Real.log (15 : ℕ)) - ((991269/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -165297/5000000) (δ := 17/1562500) 109 47
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos109_br_16 :
    |Real.cos (((109:ℕ):ℝ) * Real.log (16 : ℕ)) - ((814299/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 1548189/10000000) (δ := 887/100000000) 109 48
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos109_br_17 :
    |Real.cos (((109:ℕ):ℝ) * Real.log (17 : ℕ)) - ((146603/250000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 590109/2500000) (δ := 77/12500000) 109 49
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos109_br_18 :
    |Real.cos (((109:ℕ):ℝ) * Real.log (18 : ℕ)) - ((157109/250000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 111407/500000) (δ := 607/100000000) 109 50
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos109_br_19 :
    |Real.cos (((109:ℕ):ℝ) * Real.log (19 : ℕ)) - ((876911/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 250699/2000000) (δ := 429/50000000) 109 51
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos109_br_20 :
    |Real.cos (((109:ℕ):ℝ) * Real.log (20 : ℕ)) - ((981849/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -238523/5000000) (δ := 779/100000000) 109 52
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos109_br_21 :
    |Real.cos (((109:ℕ):ℝ) * Real.log (21 : ℕ)) - ((403117/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -2889689/10000000) (δ := 683/100000000) 109 53
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos109_br_22 :
    |Real.cos (((109:ℕ):ℝ) * Real.log (22 : ℕ)) - ((-71567/100000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -1480237/2500000) (δ := 29/5000000) 109 54
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos109_br_23 :
    |Real.cos (((109:ℕ):ℝ) * Real.log (23 : ℕ)) - ((-787083/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 6192157/10000000) (δ := 933/100000000) 109 54
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos109_br_24 :
    |Real.cos (((109:ℕ):ℝ) * Real.log (24 : ℕ)) - ((672899/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 2081689/10000000) (δ := 381/50000000) 109 55
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos109_br_25 :
    |Real.cos (((109:ℕ):ℝ) * Real.log (25 : ℕ)) - ((269767/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -2502281/10000000) (δ := 831/100000000) 109 56
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos109_br_26 :
    |Real.cos (((109:ℕ):ℝ) * Real.log (26 : ℕ)) - ((-247807/250000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -37613/50000) (δ := 691/100000000) 109 57
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos109_br_27 :
    |Real.cos (((109:ℕ):ℝ) * Real.log (27 : ℕ)) - ((224721/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 2761639/10000000) (δ := 173/25000000) 109 57
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos109_br_28 :
    |Real.cos (((109:ℕ):ℝ) * Real.log (28 : ℕ)) - ((174423/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -3036141/10000000) (δ := 1/100000) 109 58
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos109_br_29 :
    |Real.cos (((109:ℕ):ℝ) * Real.log (29 : ℕ)) - ((-862253/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 1631561/2500000) (δ := 77/10000000) 109 58
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos109_br_30 :
    |Real.cos (((109:ℕ):ℝ) * Real.log (30 : ℕ)) - ((199949/200000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 56453/10000000) (δ := 27/3125000) 109 59
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos109_br_31 :
    |Real.cos (((109:ℕ):ℝ) * Real.log (31 : ℕ)) - ((-449113/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -6716283/10000000) (δ := 131/12500000) 109 60
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos109_br_32 :
    |Real.cos (((109:ℕ):ℝ) * Real.log (32 : ℕ)) - ((357527/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 1935237/10000000) (δ := 539/50000000) 109 60
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos109_br_33 :
    |Real.cos (((109:ℕ):ℝ) * Real.log (33 : ℕ)) - ((-275759/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -5387449/10000000) (δ := 133/20000000) 109 61
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos109_br_34 :
    |Real.cos (((109:ℕ):ℝ) * Real.log (34 : ℕ)) - ((454493/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 2747483/10000000) (δ := 53/6250000) 109 61
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos109_br_35 :
    |Real.cos (((109:ℕ):ℝ) * Real.log (35 : ℕ)) - ((-438343/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -39542/78125) (δ := 333/50000000) 109 62
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos109_br_36 :
    |Real.cos (((109:ℕ):ℝ) * Real.log (36 : ℕ)) - ((125243/250000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 653797/2500000) (δ := 677/100000000) 109 62
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos109_br_37 :
    |Real.cos (((109:ℕ):ℝ) * Real.log (37 : ℕ)) - ((-628657/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -1125311/2000000) (δ := 483/50000000) 109 63
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos109_br_38 :
    |Real.cos (((109:ℕ):ℝ) * Real.log (38 : ℕ)) - ((396153/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 820271/5000000) (δ := 627/100000000) 109 63
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos109_br_39 :
    |Real.cos (((109:ℕ):ℝ) * Real.log (39 : ℕ)) - ((-940753/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -6989101/10000000) (δ := 303/50000000) 109 64
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos109_br_40 :
    |Real.cos (((109:ℕ):ℝ) * Real.log (40 : ℕ)) - ((124919/125000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -44999/5000000) (δ := 587/100000000) 109 64
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos109_br_41 :
    |Real.cos (((109:ℕ):ℝ) * Real.log (41 : ℕ)) - ((-884163/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 6638739/10000000) (δ := 727/100000000) 109 64
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos109_br_42 :
    |Real.cos (((109:ℕ):ℝ) * Real.log (42 : ℕ)) - ((539413/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -1251321/5000000) (δ := 183/20000000) 109 65
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos109_br_43 :
    |Real.cos (((109:ℕ):ℝ) * Real.log (43 : ℕ)) - ((7029/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 3909419/10000000) (δ := 37/4000000) 109 65
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos109_br_44 :
    |Real.cos (((109:ℕ):ℝ) * Real.log (44 : ℕ)) - ((-59941/100000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -5533901/10000000) (δ := 93/12500000) 109 66
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos109_br_45 :
    |Real.cos (((109:ℕ):ℝ) * Real.log (45 : ℕ)) - ((486143/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 4609/78125) (δ := 949/100000000) 109 66
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos109_br_46 :
    |Real.cos (((109:ℕ):ℝ) * Real.log (46 : ℕ)) - ((-218197/250000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 1644801/2500000) (δ := 1019/100000000) 109 66
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos109_br_47 :
    |Real.cos (((109:ℕ):ℝ) * Real.log (47 : ℕ)) - ((16277/62500 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -1634159/5000000) (δ := 1093/100000000) 109 67
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos109_br_48 :
    |Real.cos (((109:ℕ):ℝ) * Real.log (48 : ℕ)) - ((550783/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 19287/78125) (δ := 993/100000000) 109 67
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos109_br_49 :
    |Real.cos (((109:ℕ):ℝ) * Real.log (49 : ℕ)) - ((-995641/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -7620471/10000000) (δ := 107/10000000) 109 68
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos109_br_50 :
    |Real.cos (((109:ℕ):ℝ) * Real.log (50 : ℕ)) - ((662913/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -1057617/5000000) (δ := 1063/100000000) 109 68
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos109_br_51 :
    |Real.cos (((109:ℕ):ℝ) * Real.log (51 : ℕ)) - ((255537/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 1640491/5000000) (δ := 763/100000000) 109 68
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos109_br_52 :
    |Real.cos (((109:ℕ):ℝ) * Real.log (52 : ℕ)) - ((-59937/62500 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -7135553/10000000) (δ := 461/50000000) 109 69
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos109_br_53 :
    |Real.cos (((109:ℕ):ℝ) * Real.log (53 : ℕ)) - ((712341/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -48623/250000) (δ := 491/50000000) 109 69
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos109_br_54 :
    |Real.cos (((109:ℕ):ℝ) * Real.log (54 : ℕ)) - ((306317/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 3148687/10000000) (δ := 37/6250000) 109 69
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos109_br_55 :
    |Real.cos (((109:ℕ):ℝ) * Real.log (55 : ℕ)) - ((-993053/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -236223/312500) (δ := 461/50000000) 109 70
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos109_br_56 :
    |Real.cos (((109:ℕ):ℝ) * Real.log (56 : ℕ)) - ((122297/250000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -1324547/5000000) (δ := 119/12500000) 109 70
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos109_br_57 :
    |Real.cos (((109:ℕ):ℝ) * Real.log (57 : ℕ)) - ((2016/3125 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 2174041/10000000) (δ := 89/12500000) 109 70
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos109_br_58 :
    |Real.cos (((109:ℕ):ℝ) * Real.log (58 : ℕ)) - ((-930039/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 6913291/10000000) (δ := 1001/100000000) 109 70
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos109_br_59 :
    |Real.cos (((109:ℕ):ℝ) * Real.log (59 : ℕ)) - ((-83681/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -4136439/10000000) (δ := 631/100000000) 109 71
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos109_br_60 :
    |Real.cos (((109:ℕ):ℝ) * Real.log (60 : ℕ)) - ((492153/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 443501/10000000) (δ := 21/3125000) 109 71
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos109_br_61 :
    |Real.cos (((109:ℕ):ℝ) * Real.log (61 : ℕ)) - ((-49631/125000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 989547/2000000) (δ := 331/50000000) 109 71
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos109_br_62 :
    |Real.cos (((109:ℕ):ℝ) * Real.log (62 : ℕ)) - ((-409853/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -1582309/2500000) (δ := 903/100000000) 109 72
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos109_br_63 :
    |Real.cos (((109:ℕ):ℝ) * Real.log (63 : ℕ)) - ((176377/250000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -1969143/10000000) (δ := 83/10000000) 109 72
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos109_br_64 :
    |Real.cos (((109:ℕ):ℝ) * Real.log (64 : ℕ)) - ((119741/200000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 580571/2500000) (δ := 873/100000000) 109 72
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos109_br_65 :
    |Real.cos (((109:ℕ):ℝ) * Real.log (65 : ℕ)) - ((-866463/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 261887/400000) (δ := 733/100000000) 109 72
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos109_br_66 :
    |Real.cos (((109:ℕ):ℝ) * Real.log (66 : ℕ)) - ((-416293/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -2500201/5000000) (δ := 659/100000000) 109 73
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos109_br_67 :
    |Real.cos (((109:ℕ):ℝ) * Real.log (67 : ℕ)) - ((935533/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -45129/500000) (δ := 889/100000000) 109 73
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos109_br_68 :
    |Real.cos (((109:ℕ):ℝ) * Real.log (68 : ℕ)) - ((155851/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 3134531/10000000) (δ := 1039/100000000) 109 73
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos109_br_69 :
    |Real.cos (((109:ℕ):ℝ) * Real.log (69 : ℕ)) - ((-478181/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 7112703/10000000) (δ := 1079/100000000) 109 73
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos109_br_70 :
    |Real.cos (((109:ℕ):ℝ) * Real.log (70 : ℕ)) - ((-294503/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -4674329/10000000) (δ := 329/50000000) 109 74
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos109_br_71 :
    |Real.cos (((109:ℕ):ℝ) * Real.log (71 : ℕ)) - ((189619/200000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -101127/1250000) (δ := 163/20000000) 109 74
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos109_br_72 :
    |Real.cos (((109:ℕ):ℝ) * Real.log (72 : ℕ)) - ((90381/250000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 600447/2000000) (δ := 227/25000000) 109 74
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos109_br_73 :
    |Real.cos (((109:ℕ):ℝ) * Real.log (73 : ℕ)) - ((-905929/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 1352183/2000000) (δ := 339/50000000) 109 74
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos109_br_74 :
    |Real.cos (((109:ℕ):ℝ) * Real.log (74 : ℕ)) - ((-501219/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -1309877/2500000) (δ := 197/20000000) 109 75
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos109_br_75 :
    |Real.cos (((109:ℕ):ℝ) * Real.log (75 : ℕ)) - ((806437/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -316347/2000000) (δ := 489/50000000) 109 75
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos109_br_76 :
    |Real.cos (((109:ℕ):ℝ) * Real.log (76 : ℕ)) - ((172187/250000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 202759/1000000) (δ := 329/50000000) 109 75
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos109_br_77 :
    |Real.cos (((109:ℕ):ℝ) * Real.log (77 : ℕ)) - ((-123427/200000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 1397433/2500000) (δ := 217/25000000) 109 75
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos109_br_78 :
    |Real.cos (((109:ℕ):ℝ) * Real.log (78 : ℕ)) - ((-877213/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -3301027/5000000) (δ := 837/100000000) 109 76
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos109_br_79 :
    |Real.cos (((109:ℕ):ℝ) * Real.log (79 : ℕ)) - ((31317/100000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -3130669/10000000) (δ := 139/25000000) 109 76
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos109_br_80 :
    |Real.cos (((109:ℕ):ℝ) * Real.log (80 : ℕ)) - ((992949/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 297049/10000000) (δ := 737/100000000) 109 76
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos109_br_81 :
    |Real.cos (((109:ℕ):ℝ) * Real.log (81 : ℕ)) - ((48883/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 1841093/5000000) (δ := 293/50000000) 109 76
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos109_br_82 :
    |Real.cos (((109:ℕ):ℝ) * Real.log (82 : ℕ)) - ((-945627/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 3512893/5000000) (δ := 597/100000000) 109 76
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos109_br_83 :
    |Real.cos (((109:ℕ):ℝ) * Real.log (83 : ℕ)) - ((-137183/250000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -5379107/10000000) (δ := 523/50000000) 109 77
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos109_br_84 :
    |Real.cos (((109:ℕ):ℝ) * Real.log (84 : ℕ)) - ((132561/200000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -1057797/5000000) (δ := 553/50000000) 109 77
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos109_br_85 :
    |Real.cos (((109:ℕ):ℝ) * Real.log (85 : ℕ)) - ((451581/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 221859/2000000) (δ := 587/100000000) 109 77
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos109_br_86 :
    |Real.cos (((109:ℕ):ℝ) * Real.log (86 : ℕ)) - ((-147253/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 2148233/5000000) (δ := 1027/100000000) 109 77
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos109_br_87 :
    |Real.cos (((109:ℕ):ℝ) * Real.log (87 : ℕ)) - ((-197353/200000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 744679/1000000) (δ := 229/25000000) 109 77
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos109_br_88 :
    |Real.cos (((109:ℕ):ℝ) * Real.log (88 : ℕ)) - ((-117203/250000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -5146853/10000000) (δ := 187/20000000) 109 78
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos109_br_89 :
    |Real.cos (((109:ℕ):ℝ) * Real.log (89 : ℕ)) - ((33851/50000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -82709/400000) (δ := 91/12500000) 109 78
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos109_br_90 :
    |Real.cos (((109:ℕ):ℝ) * Real.log (90 : ℕ)) - ((184921/200000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 977/10000) (δ := 379/50000000) 109 78
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos109_br_91 :
    |Real.cos (((109:ℕ):ℝ) * Real.log (91 : ℕ)) - ((-24433/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 49851/125000) (δ := 569/50000000) 109 78
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos109_br_92 :
    |Real.cos (((109:ℕ):ℝ) * Real.log (92 : ℕ)) - ((-187523/200000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 1741563/2500000) (δ := 207/25000000) 109 78
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos109_br_93 :
    |Real.cos (((109:ℕ):ℝ) * Real.log (93 : ℕ)) - ((-339903/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -5795737/10000000) (δ := 247/25000000) 109 79
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos109_br_94 :
    |Real.cos (((109:ℕ):ℝ) * Real.log (94 : ℕ)) - ((406197/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -288127/1000000) (δ := 449/50000000) 109 79
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos109_br_95 :
    |Real.cos (((109:ℕ):ℝ) * Real.log (95 : ℕ)) - ((1/1 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 1177/5000000) (δ := 121/12500000) 109 79
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos109_br_96 :
    |Real.cos (((109:ℕ):ℝ) * Real.log (96 : ℕ)) - ((415491/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 356973/1250000) (δ := 499/50000000) 109 79
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos109_br_97 :
    |Real.cos (((109:ℕ):ℝ) * Real.log (97 : ℕ)) - ((-645029/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 5679643/10000000) (δ := 419/50000000) 109 79
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos109_br_98 :
    |Real.cos (((109:ℕ):ℝ) * Real.log (98 : ℕ)) - ((-969351/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -452089/625000) (δ := 839/100000000) 109 80
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos109_br_99 :
    |Real.cos (((109:ℕ):ℝ) * Real.log (99 : ℕ)) - ((-21429/100000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -4466903/10000000) (δ := 287/50000000) 109 80
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos109_br_100 :
    |Real.cos (((109:ℕ):ℝ) * Real.log (100 : ℕ)) - ((385217/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -864093/5000000) (δ := 929/100000000) 109 80
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.cos109_br_100
end AxiomAudit
