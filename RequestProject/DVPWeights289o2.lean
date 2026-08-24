import RequestProject.DVPLogBracket
import RequestProject.DVPWeights58

/-!
# Weight-bracket complement for rung-144.5
-/

noncomputable section

namespace CriticalLinePhasor.DVP

theorem wbr_2_6 :
    ((6597539/10000000 : ℚ) : ℝ) ≤ ((2 : ℕ) : ℝ) ^ (-(((6 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((2 : ℕ) : ℝ) ^ (-(((6 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((329877/500000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_3_5 :
    ((2886751/5000000 : ℚ) : ℝ) ≤ ((3 : ℕ) : ℝ) ^ (-(((5 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((3 : ℕ) : ℝ) ^ (-(((5 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((5773503/10000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_3_6 :
    ((2586409/5000000 : ℚ) : ℝ) ≤ ((3 : ℕ) : ℝ) ^ (-(((6 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((3 : ℕ) : ℝ) ^ (-(((6 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((5172819/10000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_4_6 :
    ((272047/625000 : ℚ) : ℝ) ≤ ((4 : ℕ) : ℝ) ^ (-(((6 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((4 : ℕ) : ℝ) ^ (-(((6 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((4352753/10000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_5_6 :
    ((3807307/10000000 : ℚ) : ℝ) ≤ ((5 : ℕ) : ℝ) ^ (-(((6 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((5 : ℕ) : ℝ) ^ (-(((6 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((951827/2500000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_6_6 :
    ((3412787/10000000 : ℚ) : ℝ) ≤ ((6 : ℕ) : ℝ) ^ (-(((6 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((6 : ℕ) : ℝ) ^ (-(((6 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((853197/2500000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_7_6 :
    ((1555647/5000000 : ℚ) : ℝ) ≤ ((7 : ℕ) : ℝ) ^ (-(((6 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((7 : ℕ) : ℝ) ^ (-(((6 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((622259/2000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_8_6 :
    ((574349/2000000 : ℚ) : ℝ) ≤ ((8 : ℕ) : ℝ) ^ (-(((6 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((8 : ℕ) : ℝ) ^ (-(((6 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((1435873/5000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_9_6 :
    ((535161/2000000 : ℚ) : ℝ) ≤ ((9 : ℕ) : ℝ) ^ (-(((6 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((9 : ℕ) : ℝ) ^ (-(((6 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((1337903/5000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_10_6 :
    ((1255943/5000000 : ℚ) : ℝ) ≤ ((10 : ℕ) : ℝ) ^ (-(((6 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((10 : ℕ) : ℝ) ^ (-(((6 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((2511887/10000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_250_5 :
    ((126491/2000000 : ℚ) : ℝ) ≤ ((250 : ℕ) : ℝ) ^ (-(((5 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((250 : ℕ) : ℝ) ^ (-(((5 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((79057/1250000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_250_6 :
    ((22757/625000 : ℚ) : ℝ) ≤ ((250 : ℕ) : ℝ) ^ (-(((6 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((250 : ℕ) : ℝ) ^ (-(((6 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((364113/10000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_250_7 :
    ((26203/1250000 : ℚ) : ℝ) ≤ ((250 : ℕ) : ℝ) ^ (-(((7 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((250 : ℕ) : ℝ) ^ (-(((7 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((1677/80000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_250_9 :
    ((69479/10000000 : ℚ) : ℝ) ≤ ((250 : ℕ) : ℝ) ^ (-(((9 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((250 : ℕ) : ℝ) ^ (-(((9 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((1737/250000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_250_11 :
    ((5757/2500000 : ℚ) : ℝ) ≤ ((250 : ℕ) : ℝ) ^ (-(((11 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((250 : ℕ) : ℝ) ^ (-(((11 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((23029/10000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_250_14 :
    ((2197/5000000 : ℚ) : ℝ) ≤ ((250 : ℕ) : ℝ) ^ (-(((14 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((250 : ℕ) : ℝ) ^ (-(((14 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((879/2000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_250_15 :
    ((2529/10000000 : ℚ) : ℝ) ≤ ((250 : ℕ) : ℝ) ^ (-(((15 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((250 : ℕ) : ℝ) ^ (-(((15 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((253/1000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_250_16 :
    ((91/625000 : ℚ) : ℝ) ≤ ((250 : ℕ) : ℝ) ^ (-(((16 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((250 : ℕ) : ℝ) ^ (-(((16 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((1457/10000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_250_17 :
    ((419/5000000 : ℚ) : ℝ) ≤ ((250 : ℕ) : ℝ) ^ (-(((17 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((250 : ℕ) : ℝ) ^ (-(((17 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((839/10000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_250_19 :
    ((277/10000000 : ℚ) : ℝ) ≤ ((250 : ℕ) : ℝ) ^ (-(((19 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((250 : ℕ) : ℝ) ^ (-(((19 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((139/5000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_250_20 :
    ((1/62500 : ℚ) : ℝ) ≤ ((250 : ℕ) : ℝ) ^ (-(((20 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((250 : ℕ) : ℝ) ^ (-(((20 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((161/10000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_250_21 :
    ((23/2500000 : ℚ) : ℝ) ≤ ((250 : ℕ) : ℝ) ^ (-(((21 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((250 : ℕ) : ℝ) ^ (-(((21 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((93/10000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_250_24 :
    ((17/10000000 : ℚ) : ℝ) ≤ ((250 : ℕ) : ℝ) ^ (-(((24 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((250 : ℕ) : ℝ) ^ (-(((24 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((9/5000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_250_25 :
    ((1/1000000 : ℚ) : ℝ) ≤ ((250 : ℕ) : ℝ) ^ (-(((25 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((250 : ℕ) : ℝ) ^ (-(((25 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((11/10000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_250_26 :
    ((1/2000000 : ℚ) : ℝ) ≤ ((250 : ℕ) : ℝ) ^ (-(((26 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((250 : ℕ) : ℝ) ^ (-(((26 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((3/5000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_250_27 :
    ((3/10000000 : ℚ) : ℝ) ≤ ((250 : ℕ) : ℝ) ^ (-(((27 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((250 : ℕ) : ℝ) ^ (-(((27 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((1/2500000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_250_29 :
    ((1/10000000 : ℚ) : ℝ) ≤ ((250 : ℕ) : ℝ) ^ (-(((29 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((250 : ℕ) : ℝ) ^ (-(((29 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((1/5000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_250_31 :
    ((0 : ℚ) : ℝ) ≤ ((250 : ℕ) : ℝ) ^ (-(((31 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((250 : ℕ) : ℝ) ^ (-(((31 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((1/10000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_250_34 :
    ((0 : ℚ) : ℝ) ≤ ((250 : ℕ) : ℝ) ^ (-(((34 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((250 : ℕ) : ℝ) ^ (-(((34 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((1/10000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_250_37 :
    ((0 : ℚ) : ℝ) ≤ ((250 : ℕ) : ℝ) ^ (-(((37 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((250 : ℕ) : ℝ) ^ (-(((37 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((1/10000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_11_6 :
    ((2372271/10000000 : ℚ) : ℝ) ≤ ((11 : ℕ) : ℝ) ^ (-(((6 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((11 : ℕ) : ℝ) ^ (-(((6 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((148267/625000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.wbr_250_37
end AxiomAudit
