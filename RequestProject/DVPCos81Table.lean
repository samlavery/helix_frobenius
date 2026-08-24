import RequestProject.DVPCosSinEval

/-!
# The cosine table at `t = 81` (rung-81)
-/

open Finset

noncomputable section

namespace CriticalLinePhasor.DVP

theorem cos81_br_2 :
    |Real.cos (((81:ℕ):ℝ) * Real.log (2 : ℕ)) - ((229899/250000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -504683/5000000) (δ := 157/25000000) 81 9
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos81_br_3 :
    |Real.cos (((81:ℕ):ℝ) * Real.log (3 : ℕ)) - ((520807/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 1278751/5000000) (δ := 173/25000000) 81 14
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos81_br_4 :
    |Real.cos (((81:ℕ):ℝ) * Real.log (4 : ℕ)) - ((43207/62500 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -2018731/10000000) (δ := 121/25000000) 81 18
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos81_br_5 :
    |Real.cos (((81:ℕ):ℝ) * Real.log (5 : ℕ)) - ((-1453/125000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -989013/2500000) (δ := 23/3125000) 81 21
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos81_br_6 :
    |Real.cos (((81:ℕ):ℝ) * Real.log (6 : ℕ)) - ((814311/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 1548137/10000000) (δ := 137/25000000) 81 23
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos81_br_7 :
    |Real.cos (((81:ℕ):ℝ) * Real.log (7 : ℕ)) - ((858177/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 1347723/10000000) (δ := 217/50000000) 81 25
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos81_br_8 :
    |Real.cos (((81:ℕ):ℝ) * Real.log (8 : ℕ)) - ((17593/50000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -3028097/10000000) (δ := 2/390625) 81 27
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos81_br_9 :
    |Real.cos (((81:ℕ):ℝ) * Real.log (9 : ℕ)) - ((-457521/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 1023001/2000000) (δ := 153/25000000) 81 28
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos81_br_10 :
    |Real.cos (((81:ℕ):ℝ) * Real.log (10 : ℕ)) - ((-403529/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -4965417/10000000) (δ := 743/100000000) 81 30
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos81_br_11 :
    |Real.cos (((81:ℕ):ℝ) * Real.log (11 : ℕ)) - ((13327/15625 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -1373069/10000000) (δ := 287/50000000) 81 31
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos81_br_12 :
    |Real.cos (((81:ℕ):ℝ) * Real.log (12 : ℕ)) - ((244217/250000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 134693/2500000) (δ := 409/100000000) 81 32
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos81_br_13 :
    |Real.cos (((81:ℕ):ℝ) * Real.log (13 : ℕ)) - ((2287/2500 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 1039457/10000000) (δ := 93/20000000) 81 33
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos81_br_14 :
    |Real.cos (((81:ℕ):ℝ) * Real.log (14 : ℕ)) - ((198171/200000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 169179/5000000) (δ := 577/100000000) 81 34
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos81_br_15 :
    |Real.cos (((81:ℕ):ℝ) * Real.log (15 : ℕ)) - ((847563/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -1398549/10000000) (δ := 51/6250000) 81 35
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos81_br_16 :
    |Real.cos (((81:ℕ):ℝ) * Real.log (16 : ℕ)) - ((-22087/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -2018731/5000000) (δ := 41/6250000) 81 36
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos81_br_17 :
    |Real.cos (((81:ℕ):ℝ) * Real.log (17 : ℕ)) - ((-988163/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -7468939/10000000) (δ := 93/20000000) 81 37
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos81_br_18 :
    |Real.cos (((81:ℕ):ℝ) * Real.log (18 : ℕ)) - ((-71399/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 102641/250000) (δ := 117/25000000) 81 37
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos81_br_19 :
    |Real.cos (((81:ℕ):ℝ) * Real.log (19 : ℕ)) - ((966007/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -653711/10000000) (δ := 639/100000000) 81 38
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos81_br_20 :
    |Real.cos (((81:ℕ):ℝ) * Real.log (20 : ℕ)) - ((-730543/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -5974783/10000000) (δ := 7/1250000) 81 39
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos81_br_21 :
    |Real.cos (((81:ℕ):ℝ) * Real.log (21 : ℕ)) - ((4353/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 1952613/5000000) (δ := 513/100000000) 81 39
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos81_br_22 :
    |Real.cos (((81:ℕ):ℝ) * Real.log (22 : ℕ)) - ((289631/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -1191217/5000000) (δ := 43/10000000) 81 40
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos81_br_23 :
    |Real.cos (((81:ℕ):ℝ) * Real.log (23 : ℕ)) - ((-110057/125000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 827381/1250000) (δ := 683/100000000) 81 40
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos81_br_24 :
    |Real.cos (((81:ℕ):ℝ) * Real.log (24 : ℕ)) - ((15349/15625 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -235297/5000000) (δ := 37/6250000) 81 41
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos81_br_25 :
    |Real.cos (((81:ℕ):ℝ) * Real.log (25 : ℕ)) - ((-99973/100000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 389793/500000) (δ := 79/12500000) 81 41
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos81_br_26 :
    |Real.cos (((81:ℕ):ℝ) * Real.log (26 : ℕ)) - ((124991/125000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 30091/10000000) (δ := 531/100000000) 81 42
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos81_br_27 :
    |Real.cos (((81:ℕ):ℝ) * Real.log (27 : ℕ)) - ((-997367/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 1918127/2500000) (δ := 133/25000000) 81 42
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos81_br_28 :
    |Real.cos (((81:ℕ):ℝ) * Real.log (28 : ℕ)) - ((241049/250000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -20969/312500) (δ := 761/100000000) 81 43
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos81_br_29 :
    |Real.cos (((81:ℕ):ℝ) * Real.log (29 : ℕ)) - ((-421597/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 1286997/2000000) (δ := 571/100000000) 81 43
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos81_br_30 :
    |Real.cos (((81:ℕ):ℝ) * Real.log (30 : ℕ)) - ((142731/250000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -481583/2000000) (δ := 623/100000000) 81 44
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos81_br_31 :
    |Real.cos (((81:ℕ):ℝ) * Real.log (31 : ℕ)) - ((-121711/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 169281/400000) (δ := 39/5000000) 81 44
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos81_br_32 :
    |Real.cos (((81:ℕ):ℝ) * Real.log (32 : ℕ)) - ((-86621/200000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -5046827/10000000) (δ := 799/100000000) 81 45
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos81_br_33 :
    |Real.cos (((81:ℕ):ℝ) * Real.log (33 : ℕ)) - ((889853/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 592217/5000000) (δ := 247/50000000) 81 45
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos81_br_34 :
    |Real.cos (((81:ℕ):ℝ) * Real.log (34 : ℕ)) - ((-968979/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 7229659/10000000) (δ := 619/100000000) 81 45
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos81_br_35 :
    |Real.cos (((81:ℕ):ℝ) * Real.log (35 : ℕ)) - ((100669/200000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -326041/1250000) (δ := 99/20000000) 81 46
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos81_br_36 :
    |Real.cos (((81:ℕ):ℝ) * Real.log (36 : ℕ)) - ((163103/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 1548137/5000000) (δ := 33/6250000) 81 46
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos81_br_37 :
    |Real.cos (((81:ℕ):ℝ) * Real.log (37 : ℕ)) - ((-950413/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -7063397/10000000) (δ := 369/50000000) 81 47
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos81_br_38 :
    |Real.cos (((81:ℕ):ℝ) * Real.log (38 : ℕ)) - ((393387/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -1663077/10000000) (δ := 91/20000000) 81 47
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos81_br_39 :
    |Real.cos (((81:ℕ):ℝ) * Real.log (39 : ℕ)) - ((13163/100000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 3596959/10000000) (δ := 117/25000000) 81 47
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos81_br_40 :
    |Real.cos (((81:ℕ):ℝ) * Real.log (40 : ℕ)) - ((-940079/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -1746037/2500000) (δ := 13/3125000) 81 48
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos81_br_41 :
    |Real.cos (((81:ℕ):ℝ) * Real.log (41 : ℕ)) - ((350657/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -991947/5000000) (δ := 129/25000000) 81 48
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos81_br_42 :
    |Real.cos (((81:ℕ):ℝ) * Real.log (42 : ℕ)) - ((400857/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 144793/500000) (δ := 697/100000000) 81 48
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos81_br_43 :
    |Real.cos (((81:ℕ):ℝ) * Real.log (43 : ℕ)) - ((-124627/125000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 3830393/5000000) (δ := 707/100000000) 81 48
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos81_br_44 :
    |Real.cos (((81:ℕ):ℝ) * Real.log (44 : ℕ)) - ((42489/200000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -16959/50000) (δ := 283/50000000) 81 49
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos81_br_45 :
    |Real.cos (((81:ℕ):ℝ) * Real.log (45 : ℕ)) - ((894457/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 579477/5000000) (δ := 727/100000000) 81 49
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos81_br_46 :
    |Real.cos (((81:ℕ):ℝ) * Real.log (46 : ℕ)) - ((-311697/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 2804841/5000000) (δ := 757/100000000) 81 49
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos81_br_47 :
    |Real.cos (((81:ℕ):ℝ) * Real.log (47 : ℕ)) - ((-166067/250000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -229731/400000) (δ := 209/25000000) 81 50
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos81_br_48 :
    |Real.cos (((81:ℕ):ℝ) * Real.log (48 : ℕ)) - ((165967/200000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -1479959/10000000) (δ := 23/3125000) 81 50
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos81_br_49 :
    |Real.cos (((81:ℕ):ℝ) * Real.log (49 : ℕ)) - ((236467/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 1347723/5000000) (δ := 757/100000000) 81 50
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos81_br_50 :
    |Real.cos (((81:ℕ):ℝ) * Real.log (50 : ℕ)) - ((-455107/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 1357299/2000000) (δ := 97/12500000) 81 50
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos81_br_51 :
    |Real.cos (((81:ℕ):ℝ) * Real.log (51 : ℕ)) - ((-1199/3125 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -4911437/10000000) (δ := 117/20000000) 81 51
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos81_br_52 :
    |Real.cos (((81:ℕ):ℝ) * Real.log (52 : ℕ)) - ((462129/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -489637/5000000) (δ := 27/4000000) 81 51
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos81_br_53 :
    |Real.cos (((81:ℕ):ℝ) * Real.log (53 : ℕ)) - ((407397/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 575597/2000000) (δ := 147/20000000) 81 51
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos81_br_54 :
    |Real.cos (((81:ℕ):ℝ) * Real.log (54 : ℕ)) - ((-888681/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 3331571/5000000) (δ := 93/20000000) 81 51
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos81_br_55 :
    |Real.cos (((81:ℕ):ℝ) * Real.log (55 : ℕ)) - ((-132977/250000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -33307/62500) (δ := 689/100000000) 81 52
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos81_br_56 :
    |Real.cos (((81:ℕ):ℝ) * Real.log (56 : ℕ)) - ((156497/200000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -1680373/10000000) (δ := 719/100000000) 81 52
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos81_br_57 :
    |Real.cos (((81:ℕ):ℝ) * Real.log (57 : ℕ)) - ((72379/100000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 1903791/10000000) (δ := 519/100000000) 81 52
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos81_br_58 :
    |Real.cos (((81:ℕ):ℝ) * Real.log (58 : ℕ)) - ((-56419/100000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 5425619/10000000) (δ := 377/50000000) 81 52
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos81_br_59 :
    |Real.cos (((81:ℕ):ℝ) * Real.log (59 : ℕ)) - ((-915799/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -6820721/10000000) (δ := 463/100000000) 81 53
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos81_br_60 :
    |Real.cos (((81:ℕ):ℝ) * Real.log (60 : ℕ)) - ((8099/40000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -10679/31250) (δ := 3/625000) 81 53
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos81_br_61 :
    |Real.cos (((81:ℕ):ℝ) * Real.log (61 : ℕ)) - ((999607/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -4381/625000) (δ := 51/10000000) 81 53
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos81_br_62 :
    |Real.cos (((81:ℕ):ℝ) * Real.log (62 : ℕ)) - ((13901/50000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 3222659/10000000) (δ := 33/5000000) 81 53
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos81_br_63 :
    |Real.cos (((81:ℕ):ℝ) * Real.log (63 : ℕ)) - ((-212277/250000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 807841/1250000) (δ := 633/100000000) 81 53
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos81_br_64 :
    |Real.cos (((81:ℕ):ℝ) * Real.log (64 : ℕ)) - ((-752389/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -6056193/10000000) (δ := 1/156250) 81 54
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos81_br_65 :
    |Real.cos (((81:ℕ):ℝ) * Real.log (65 : ℕ)) - ((78649/200000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -583319/2000000) (δ := 27/5000000) 81 54
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos81_br_66 :
    |Real.cos (((81:ℕ):ℝ) * Real.log (66 : ℕ)) - ((997549/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 43767/2500000) (δ := 503/100000000) 81 54
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos81_br_67 :
    |Real.cos (((81:ℕ):ℝ) * Real.log (67 : ℕ)) - ((278951/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 1610119/5000000) (δ := 693/100000000) 81 54
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos81_br_68 :
    |Real.cos (((81:ℕ):ℝ) * Real.log (68 : ℕ)) - ((-99247/125000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 6220293/10000000) (δ := 803/100000000) 81 54
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos81_br_69 :
    |Real.cos (((81:ℕ):ℝ) * Real.log (69 : ℕ)) - ((-431649/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -6531413/10000000) (δ := 99/12500000) 81 55
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos81_br_70 :
    |Real.cos (((81:ℕ):ℝ) * Real.log (70 : ℕ)) - ((123403/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -1808847/5000000) (δ := 251/50000000) 81 55
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos81_br_71 :
    |Real.cos (((81:ℕ):ℝ) * Real.log (71 : ℕ)) - ((95589/100000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -149061/2000000) (δ := 611/100000000) 81 55
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos81_br_72 :
    |Real.cos (((81:ℕ):ℝ) * Real.log (72 : ℕ)) - ((671353/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 2086909/10000000) (δ := 21/3125000) 81 55
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos81_br_73 :
    |Real.cos (((81:ℕ):ℝ) * Real.log (73 : ℕ)) - ((-372059/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 4880057/10000000) (δ := 241/50000000) 81 55
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos81_br_74 :
    |Real.cos (((81:ℕ):ℝ) * Real.log (74 : ℕ)) - ((-996173/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 7635201/10000000) (δ := 731/100000000) 81 55
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos81_br_75 :
    |Real.cos (((81:ℕ):ℝ) * Real.log (75 : ℕ)) - ((-540511/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -5354601/10000000) (δ := 741/100000000) 81 56
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos81_br_76 :
    |Real.cos (((81:ℕ):ℝ) * Real.log (76 : ℕ)) - ((240511/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -1336221/5000000) (δ := 501/100000000) 81 56
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos81_br_77 :
    |Real.cos (((81:ℕ):ℝ) * Real.log (77 : ℕ)) - ((999949/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -12673/5000000) (δ := 671/100000000) 81 56
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos81_br_78 :
    |Real.cos (((81:ℕ):ℝ) * Real.log (78 : ℕ)) - ((255247/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 1293797/5000000) (δ := 611/100000000) 81 56
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos81_br_79 :
    |Real.cos (((81:ℕ):ℝ) * Real.log (79 : ℕ)) - ((-238001/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 5167247/10000000) (δ := 211/50000000) 81 56
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos81_br_80 :
    |Real.cos (((81:ℕ):ℝ) * Real.log (80 : ℕ)) - ((-998443/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 154289/200000) (δ := 551/100000000) 81 56
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos81_br_81 :
    |Real.cos (((81:ℕ):ℝ) * Real.log (81 : ℕ)) - ((-145337/250000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -5477953/10000000) (δ := 211/50000000) 81 57
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos81_br_82 :
    |Real.cos (((81:ℕ):ℝ) * Real.log (82 : ℕ)) - ((36487/100000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -2993259/10000000) (δ := 441/100000000) 81 57
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos81_br_83 :
    |Real.cos (((81:ℕ):ℝ) * Real.log (83 : ℕ)) - ((1563/1600 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -134671/2500000) (δ := 781/100000000) 81 57
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos81_br_84 :
    |Real.cos (((81:ℕ):ℝ) * Real.log (84 : ℕ)) - ((728547/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 377299/2000000) (δ := 841/100000000) 81 57
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos81_br_85 :
    |Real.cos (((81:ℕ):ℝ) * Real.log (85 : ℕ)) - ((-17739/125000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 4282973/10000000) (δ := 113/25000000) 81 57
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos81_br_86 :
    |Real.cos (((81:ℕ):ℝ) * Real.log (86 : ℕ)) - ((-886521/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 6651421/10000000) (δ := 193/25000000) 81 57
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos81_br_87 :
    |Real.cos (((81:ℕ):ℝ) * Real.log (87 : ℕ)) - ((-224521/250000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -1678869/2500000) (δ := 17/2500000) 81 58
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos81_br_88 :
    |Real.cos (((81:ℕ):ℝ) * Real.log (88 : ℕ)) - ((-37707/200000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -880233/2000000) (δ := 71/10000000) 81 58
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos81_br_89 :
    |Real.cos (((81:ℕ):ℝ) * Real.log (89 : ℕ)) - ((33179/50000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -422601/2000000) (δ := 553/100000000) 81 58
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos81_br_90 :
    |Real.cos (((81:ℕ):ℝ) * Real.log (90 : ℕ)) - ((99821/100000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 37397/2500000) (δ := 543/100000000) 81 58
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos81_br_91 :
    |Real.cos (((81:ℕ):ℝ) * Real.log (91 : ℕ)) - ((577713/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 119359/500000) (δ := 843/100000000) 81 58
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos81_br_92 :
    |Real.cos (((81:ℕ):ℝ) * Real.log (92 : ℕ)) - ((-133043/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 4600317/10000000) (δ := 613/100000000) 81 58
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos81_br_93 :
    |Real.cos (((81:ℕ):ℝ) * Real.log (93 : ℕ)) - ((-227679/250000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 6789527/10000000) (δ := 723/100000000) 81 58
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos81_br_94 :
    |Real.cos (((81:ℕ):ℝ) * Real.log (94 : ℕ)) - ((-904523/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -10551/15625) (δ := 161/25000000) 81 59
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos81_br_95 :
    |Real.cos (((81:ℕ):ℝ) * Real.log (95 : ℕ)) - ((-134863/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -4609763/10000000) (δ := 357/50000000) 81 59
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos81_br_96 :
    |Real.cos (((81:ℕ):ℝ) * Real.log (96 : ℕ)) - ((54389/100000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -99573/400000) (δ := 11/1562500) 81 59
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos81_br_97 :
    |Real.cos (((81:ℕ):ℝ) * Real.log (97 : ℕ)) - ((987803/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -19543/500000) (δ := 39/6250000) 81 59
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos81_br_98 :
    |Real.cos (((81:ℕ):ℝ) * Real.log (98 : ℕ)) - ((390531/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 1686081/10000000) (δ := 307/50000000) 81 59
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos81_br_99 :
    |Real.cos (((81:ℕ):ℝ) * Real.log (99 : ℕ)) - ((36977/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 233871/625000) (δ := 439/100000000) 81 59
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos81_br_100 :
    |Real.cos (((81:ℕ):ℝ) * Real.log (100 : ℕ)) - ((-674329/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 5777129/10000000) (δ := 83/12500000) 81 59
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.cos81_br_100
end AxiomAudit
