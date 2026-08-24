import RequestProject.DVPCosSinEval

/-!
# The cosine table at `t = 91` (rung-91)
-/

open Finset

noncomputable section

namespace CriticalLinePhasor.DVP

theorem cos91_br_2 :
    |Real.cos (((91:ℕ):ℝ) * Real.log (2 : ℕ)) - ((970249/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 12227/200000) (δ := 699/100000000) 91 10
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos91_br_3 :
    |Real.cos (((91:ℕ):ℝ) * Real.log (3 : ℕ)) - ((424357/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -1393117/10000000) (δ := 793/100000000) 91 16
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos91_br_4 :
    |Real.cos (((91:ℕ):ℝ) * Real.log (4 : ℕ)) - ((176553/200000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 1222701/10000000) (δ := 263/50000000) 91 20
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos91_br_5 :
    |Real.cos (((91:ℕ):ℝ) * Real.log (5 : ℕ)) - ((-183039/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 4863969/10000000) (δ := 167/20000000) 91 23
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos91_br_6 :
    |Real.cos (((91:ℕ):ℝ) * Real.log (6 : ℕ)) - ((59469/62500 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -390883/5000000) (δ := 31/5000000) 91 26
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos91_br_7 :
    |Real.cos (((91:ℕ):ℝ) * Real.log (7 : ℕ)) - ((409733/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 2871587/10000000) (δ := 481/100000000) 91 28
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos91_br_8 :
    |Real.cos (((91:ℕ):ℝ) * Real.log (8 : ℕ)) - ((148551/200000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 458513/2500000) (δ := 7/1250000) 91 30
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos91_br_9 :
    |Real.cos (((91:ℕ):ℝ) * Real.log (9 : ℕ)) - ((55079/125000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -1393117/5000000) (δ := 337/50000000) 91 32
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos91_br_10 :
    |Real.cos (((91:ℕ):ℝ) * Real.log (10 : ℕ)) - ((-580491/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 136883/250000) (δ := 163/20000000) 91 33
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos91_br_11 :
    |Real.cos (((91:ℕ):ℝ) * Real.log (11 : ℕ)) - ((-26367/200000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -212877/500000) (δ := 657/100000000) 91 35
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos91_br_12 :
    |Real.cos (((91:ℕ):ℝ) * Real.log (12 : ℕ)) - ((498839/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -34083/2000000) (δ := 233/50000000) 91 36
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos91_br_13 :
    |Real.cos (((91:ℕ):ℝ) * Real.log (13 : ℕ)) - ((2979/5000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 2331337/10000000) (δ := 61/12500000) 91 37
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos91_br_14 :
    |Real.cos (((91:ℕ):ℝ) * Real.log (14 : ℕ)) - ((176689/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 1741469/5000000) (δ := 327/50000000) 91 38
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos91_br_15 :
    |Real.cos (((91:ℕ):ℝ) * Real.log (15 : ℕ)) - ((45361/250000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 3470853/10000000) (δ := 913/100000000) 91 39
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos91_br_16 :
    |Real.cos (((91:ℕ):ℝ) * Real.log (16 : ℕ)) - ((558549/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 2445403/10000000) (δ := 733/100000000) 91 40
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos91_br_17 :
    |Real.cos (((91:ℕ):ℝ) * Real.log (17 : ℕ)) - ((977651/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 529541/10000000) (δ := 271/50000000) 91 41
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos91_br_18 :
    |Real.cos (((91:ℕ):ℝ) * Real.log (18 : ℕ)) - ((322431/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -2174883/10000000) (δ := 251/50000000) 91 42
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos91_br_19 :
    |Real.cos (((91:ℕ):ℝ) * Real.log (19 : ℕ)) - ((-614873/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -5582553/10000000) (δ := 89/12500000) 91 43
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos91_br_20 :
    |Real.cos (((91:ℕ):ℝ) * Real.log (20 : ℕ)) - ((-760363/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 6086671/10000000) (δ := 321/50000000) 91 43
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos91_br_21 :
    |Real.cos (((91:ℕ):ℝ) * Real.log (21 : ℕ)) - ((103771/125000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 147847/1000000) (δ := 3/500000) 91 44
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos91_br_22 :
    |Real.cos (((91:ℕ):ℝ) * Real.log (22 : ℕ)) - ((22417/200000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -3646189/10000000) (δ := 121/25000000) 91 45
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos91_br_23 :
    |Real.cos (((91:ℕ):ℝ) * Real.log (23 : ℕ)) - ((-849923/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 6466587/10000000) (δ := 769/100000000) 91 45
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos91_br_24 :
    |Real.cos (((91:ℕ):ℝ) * Real.log (24 : ℕ)) - ((492243/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 55117/1250000) (δ := 319/50000000) 91 46
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos91_br_25 :
    |Real.cos (((91:ℕ):ℝ) * Real.log (25 : ℕ)) - ((-731973/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -747503/1250000) (δ := 177/25000000) 91 47
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos91_br_26 :
    |Real.cos (((91:ℕ):ℝ) * Real.log (26 : ℕ)) - ((383627/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 91959/312500) (δ := 299/50000000) 91 47
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos91_br_27 :
    |Real.cos (((91:ℕ):ℝ) * Real.log (27 : ℕ)) - ((-25193/250000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -83587/200000) (δ := 149/25000000) 91 48
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos91_br_28 :
    |Real.cos (((91:ℕ):ℝ) * Real.log (28 : ℕ)) - ((-66869/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 4094289/10000000) (δ := 827/100000000) 91 48
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos91_br_29 :
    |Real.cos (((91:ℕ):ℝ) * Real.log (29 : ℕ)) - ((118359/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -3630399/10000000) (δ := 323/50000000) 91 49
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos91_br_30 :
    |Real.cos (((91:ℕ):ℝ) * Real.log (30 : ℕ)) - ((-12409/200000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 1020551/2500000) (δ := 737/100000000) 91 49
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos91_br_31 :
    |Real.cos (((91:ℕ):ℝ) * Real.log (31 : ℕ)) - ((-1492/15625 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -166643/400000) (δ := 7/781250) 91 50
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos91_br_32 :
    |Real.cos (((91:ℕ):ℝ) * Real.log (32 : ℕ)) - ((341107/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 1528377/5000000) (δ := 453/50000000) 91 50
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos91_br_33 :
    |Real.cos (((91:ℕ):ℝ) * Real.log (33 : ℕ)) - ((-318063/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -5650657/10000000) (δ := 269/50000000) 91 51
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos91_br_34 :
    |Real.cos (((91:ℕ):ℝ) * Real.log (34 : ℕ)) - ((14026/15625 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 285223/2500000) (δ := 143/20000000) 91 51
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos91_br_35 :
    |Real.cos (((91:ℕ):ℝ) * Real.log (35 : ℕ)) - ((-499439/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 7735557/10000000) (δ := 137/25000000) 91 51
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos91_br_36 :
    |Real.cos (((91:ℕ):ℝ) * Real.log (36 : ℕ)) - ((405361/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -390883/2500000) (δ := 73/12500000) 91 52
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos91_br_37 :
    |Real.cos (((91:ℕ):ℝ) * Real.log (37 : ℕ)) - ((-146373/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 933947/2000000) (δ := 201/25000000) 91 52
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos91_br_38 :
    |Real.cos (((91:ℕ):ℝ) * Real.log (38 : ℕ)) - ((-81129/200000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -2485601/5000000) (δ := 27/5000000) 91 53
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos91_br_39 :
    |Real.cos (((91:ℕ):ℝ) * Real.log (39 : ℕ)) - ((465201/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 938221/10000000) (δ := 503/100000000) 91 53
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos91_br_40 :
    |Real.cos (((91:ℕ):ℝ) * Real.log (40 : ℕ)) - ((-55937/62500 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 3349011/5000000) (δ := 47/10000000) 91 53
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos91_br_41 :
    |Real.cos (((91:ℕ):ℝ) * Real.log (41 : ℕ)) - ((212221/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -848093/2500000) (δ := 29/5000000) 91 54
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos91_br_42 :
    |Real.cos (((91:ℕ):ℝ) * Real.log (42 : ℕ)) - ((670489/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 2089821/10000000) (δ := 773/100000000) 91 54
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos91_br_43 :
    |Real.cos (((91:ℕ):ℝ) * Real.log (43 : ℕ)) - ((-986519/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 7443009/10000000) (δ := 803/100000000) 91 54
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos91_br_44 :
    |Real.cos (((91:ℕ):ℝ) * Real.log (44 : ℕ)) - ((174667/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -3034839/10000000) (δ := 321/50000000) 91 55
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos91_br_45 :
    |Real.cos (((91:ℕ):ℝ) * Real.log (45 : ℕ)) - ((168517/250000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 259717/1250000) (δ := 791/100000000) 91 55
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos91_br_46 :
    |Real.cos (((91:ℕ):ℝ) * Real.log (46 : ℕ)) - ((-476103/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 7077937/10000000) (δ := 841/100000000) 91 55
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos91_br_47 :
    |Real.cos (((91:ℕ):ℝ) * Real.log (47 : ℕ)) - ((37889/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -934341/2500000) (δ := 911/100000000) 91 56
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos91_br_48 :
    |Real.cos (((91:ℕ):ℝ) * Real.log (48 : ℕ)) - ((228179/250000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 526143/5000000) (δ := 851/100000000) 91 56
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos91_br_49 :
    |Real.cos (((91:ℕ):ℝ) * Real.log (49 : ℕ)) - ((-664237/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 2871587/5000000) (δ := 431/50000000) 91 56
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos91_br_50 :
    |Real.cos (((91:ℕ):ℝ) * Real.log (50 : ℕ)) - ((-272619/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -5368673/10000000) (δ := 881/100000000) 91 57
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos91_br_51 :
    |Real.cos (((91:ℕ):ℝ) * Real.log (51 : ℕ)) - ((94093/100000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -34543/400000) (δ := 621/100000000) 91 57
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos91_br_52 :
    |Real.cos (((91:ℕ):ℝ) * Real.log (52 : ℕ)) - ((37157/250000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 3554039/10000000) (δ := 771/100000000) 91 57
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos91_br_53 :
    |Real.cos (((91:ℕ):ℝ) * Real.log (53 : ℕ)) - ((-99991/100000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -391023/500000) (δ := 41/5000000) 91 58
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos91_br_54 :
    |Real.cos (((91:ℕ):ℝ) * Real.log (54 : ℕ)) - ((2236/15625 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -3567999/10000000) (δ := 49/10000000) 91 58
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos91_br_55 :
    |Real.cos (((91:ℕ):ℝ) * Real.log (55 : ℕ)) - ((970723/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 60643/1000000) (δ := 773/100000000) 91 58
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos91_br_56 :
    |Real.cos (((91:ℕ):ℝ) * Real.log (56 : ℕ)) - ((-19153/62500 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 117641/250000) (δ := 823/100000000) 91 58
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos91_br_57 :
    |Real.cos (((91:ℕ):ℝ) * Real.log (57 : ℕ)) - ((-469459/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -697567/1000000) (δ := 297/50000000) 91 59
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos91_br_58 :
    |Real.cos (((91:ℕ):ℝ) * Real.log (58 : ℕ)) - ((177623/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -377381/1250000) (δ := 819/100000000) 91 59
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos91_br_59 :
    |Real.cos (((91:ℕ):ℝ) * Real.log (59 : ℕ)) - ((188013/200000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 173987/2000000) (δ := 539/100000000) 91 59
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos91_br_60 :
    |Real.cos (((91:ℕ):ℝ) * Real.log (60 : ℕ)) - ((-301843/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 938711/2000000) (δ := 141/25000000) 91 59
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos91_br_61 :
    |Real.cos (((91:ℕ):ℝ) * Real.log (61 : ℕ)) - ((-971339/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -906749/1250000) (δ := 117/20000000) 91 60
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos91_br_62 :
    |Real.cos (((91:ℕ):ℝ) * Real.log (62 : ℕ)) - ((148357/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -888681/2500000) (δ := 151/20000000) 91 60
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos91_br_63 :
    |Real.cos (((91:ℕ):ℝ) * Real.log (63 : ℕ)) - ((999417/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 42677/5000000) (δ := 339/50000000) 91 60
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos91_br_64 :
    |Real.cos (((91:ℕ):ℝ) * Real.log (64 : ℕ)) - ((103369/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 733621/2000000) (δ := 149/20000000) 91 60
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos91_br_65 :
    |Real.cos (((91:ℕ):ℝ) * Real.log (65 : ℕ)) - ((-241373/250000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 7195307/10000000) (δ := 121/20000000) 91 60
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos91_br_66 :
    |Real.cos (((91:ℕ):ℝ) * Real.log (66 : ℕ)) - ((-430391/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -2519653/5000000) (δ := 137/25000000) 91 61
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos91_br_67 :
    |Real.cos (((91:ℕ):ℝ) * Real.log (67 : ℕ)) - ((79773/100000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -1618189/10000000) (δ := 379/50000000) 91 61
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos91_br_68 :
    |Real.cos (((91:ℕ):ℝ) * Real.log (68 : ℕ)) - ((95533/125000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 1752243/10000000) (δ := 111/12500000) 91 61
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos91_br_69 :
    |Real.cos (((91:ℕ):ℝ) * Real.log (69 : ℕ)) - ((-221343/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 507347/1000000) (δ := 111/12500000) 91 61
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos91_br_70 :
    |Real.cos (((91:ℕ):ℝ) * Real.log (70 : ℕ)) - ((-1569/1600 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -230033/312500) (δ := 567/100000000) 91 62
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos91_br_71 :
    |Real.cos (((91:ℕ):ℝ) * Real.log (71 : ℕ)) - ((-82729/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -4134051/10000000) (δ := 343/50000000) 91 62
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos91_br_72 :
    |Real.cos (((91:ℕ):ℝ) * Real.log (72 : ℕ)) - ((928341/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -952181/10000000) (δ := 757/100000000) 91 62
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos91_br_73 :
    |Real.cos (((91:ℕ):ℝ) * Real.log (73 : ℕ)) - ((641519/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 10929/50000) (δ := 547/100000000) 91 62
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos91_br_74 :
    |Real.cos (((91:ℕ):ℝ) * Real.log (74 : ℕ)) - ((-25777/50000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 2640543/5000000) (δ := 423/50000000) 91 62
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos91_br_75 :
    |Real.cos (((91:ℕ):ℝ) * Real.log (75 : ℕ)) - ((-24539/25000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -7373141/10000000) (δ := 413/50000000) 91 63
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos91_br_76 :
    |Real.cos (((91:ℕ):ℝ) * Real.log (76 : ℕ)) - ((-4307/25000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -4359851/10000000) (δ := 273/50000000) 91 63
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos91_br_77 :
    |Real.cos (((91:ℕ):ℝ) * Real.log (77 : ℕ)) - ((425113/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -1385953/10000000) (δ := 23/3125000) 91 63
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos91_br_78 :
    |Real.cos (((91:ℕ):ℝ) * Real.log (78 : ℕ)) - ((406989/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 387393/2500000) (δ := 169/25000000) 91 63
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos91_br_79 :
    |Real.cos (((91:ℕ):ℝ) * Real.log (79 : ℕ)) - ((-206781/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 44477/100000) (δ := 457/100000000) 91 63
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos91_br_80 :
    |Real.cos (((91:ℕ):ℝ) * Real.log (80 : ℕ)) - ((-488183/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 7309373/10000000) (δ := 77/12500000) 91 63
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos91_br_81 :
    |Real.cos (((91:ℕ):ℝ) * Real.log (81 : ℕ)) - ((-305843/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -5572467/10000000) (δ := 477/100000000) 91 64
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos91_br_82 :
    |Real.cos (((91:ℕ):ℝ) * Real.log (82 : ℕ)) - ((442503/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -2781021/10000000) (δ := 253/50000000) 91 64
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos91_br_83 :
    |Real.cos (((91:ℕ):ℝ) * Real.log (83 : ℕ)) - ((249989/250000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -23411/10000000) (δ := 423/50000000) 91 64
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos91_br_84 :
    |Real.cos (((91:ℕ):ℝ) * Real.log (84 : ℕ)) - ((94183/200000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 675293/2500000) (δ := 473/50000000) 91 64
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos91_br_85 :
    |Real.cos (((91:ℕ):ℝ) * Real.log (85 : ℕ)) - ((-553539/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 5393511/10000000) (δ := 487/100000000) 91 64
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos91_br_86 :
    |Real.cos (((91:ℕ):ℝ) * Real.log (86 : ℕ)) - ((-99679/100000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -7653603/10000000) (δ := 429/50000000) 91 65
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos91_br_87 :
    |Real.cos (((91:ℕ):ℝ) * Real.log (87 : ℕ)) - ((-212341/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -1255879/2500000) (δ := 153/20000000) 91 65
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos91_br_88 :
    |Real.cos (((91:ℕ):ℝ) * Real.log (88 : ℕ)) - ((282899/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -37867/156250) (δ := 163/20000000) 91 65
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos91_br_89 :
    |Real.cos (((91:ℕ):ℝ) * Real.log (89 : ℕ)) - ((249567/250000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 147161/10000000) (δ := 19/3125000) 91 65
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos91_br_90 :
    |Real.cos (((91:ℕ):ℝ) * Real.log (90 : ℕ)) - ((237587/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 2689087/10000000) (δ := 309/50000000) 91 65
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos91_br_91 :
    |Real.cos (((91:ℕ):ℝ) * Real.log (91 : ℕ)) - ((-488503/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 208117/400000) (δ := 479/50000000) 91 65
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos91_br_92 :
    |Real.cos (((91:ℕ):ℝ) * Real.log (92 : ℕ)) - ((-997831/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 961161/1250000) (δ := 167/25000000) 91 65
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos91_br_93 :
    |Real.cos (((91:ℕ):ℝ) * Real.log (93 : ℕ)) - ((-607477/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -5559191/10000000) (δ := 849/100000000) 91 66
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos91_br_94 :
    |Real.cos (((91:ℕ):ℝ) * Real.log (94 : ℕ)) - ((157469/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -3126013/10000000) (δ := 739/100000000) 91 66
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos91_br_95 :
    |Real.cos (((91:ℕ):ℝ) * Real.log (95 : ℕ)) - ((38359/40000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -718583/10000000) (δ := 829/100000000) 91 66
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos91_br_96 :
    |Real.cos (((91:ℕ):ℝ) * Real.log (96 : ℕ)) - ((196659/250000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 1663637/10000000) (δ := 799/100000000) 91 66
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos91_br_97 :
    |Real.cos (((91:ℕ):ℝ) * Real.log (97 : ℕ)) - ((-37663/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 4021171/10000000) (δ := 679/100000000) 91 66
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos91_br_98 :
    |Real.cos (((91:ℕ):ℝ) * Real.log (98 : ℕ)) - ((-412729/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 254181/400000) (δ := 689/100000000) 91 66
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos91_br_99 :
    |Real.cos (((91:ℕ):ℝ) * Real.log (99 : ℕ)) - ((-947943/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -3521887/5000000) (δ := 493/100000000) 91 67
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos91_br_100 :
    |Real.cos (((91:ℕ):ℝ) * Real.log (100 : ℕ)) - ((-16303/50000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -2378661/5000000) (δ := 77/10000000) 91 67
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.cos91_br_100
end AxiomAudit
