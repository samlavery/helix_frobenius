import RequestProject.DVPLogBracket
import RequestProject.DVPWeights58

/-!
# Weight-bracket column at `n = 1000` (N = 1000 segment tier)
-/

noncomputable section

namespace CriticalLinePhasor.DVP

theorem wbr_1000_5 :
    ((3162277/100000000 : ℚ) : ℝ) ≤ ((1000 : ℕ) : ℝ) ^ (-(((5 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((1000 : ℕ) : ℝ) ^ (-(((5 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((1581139/50000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_1000_6 :
    ((1584893/100000000 : ℚ) : ℝ) ≤ ((1000 : ℕ) : ℝ) ^ (-(((6 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((1000 : ℕ) : ℝ) ^ (-(((6 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((792447/50000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_1000_7 :
    ((99291/12500000 : ℚ) : ℝ) ≤ ((1000 : ℕ) : ℝ) ^ (-(((7 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((1000 : ℕ) : ℝ) ^ (-(((7 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((794329/100000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_1000_9 :
    ((99763/50000000 : ℚ) : ℝ) ≤ ((1000 : ℕ) : ℝ) ^ (-(((9 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((1000 : ℕ) : ℝ) ^ (-(((9 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((199527/100000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_1000_11 :
    ((25059/50000000 : ℚ) : ℝ) ≤ ((1000 : ℕ) : ℝ) ^ (-(((11 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((1000 : ℕ) : ℝ) ^ (-(((11 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((50119/100000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_1000_14 :
    ((6309/100000000 : ℚ) : ℝ) ≤ ((1000 : ℕ) : ℝ) ^ (-(((14 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((1000 : ℕ) : ℝ) ^ (-(((14 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((631/10000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_1000_15 :
    ((1581/50000000 : ℚ) : ℝ) ≤ ((1000 : ℕ) : ℝ) ^ (-(((15 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((1000 : ℕ) : ℝ) ^ (-(((15 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((3163/100000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_1000_16 :
    ((99/6250000 : ℚ) : ℝ) ≤ ((1000 : ℕ) : ℝ) ^ (-(((16 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((1000 : ℕ) : ℝ) ^ (-(((16 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((317/20000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_1000_17 :
    ((397/50000000 : ℚ) : ℝ) ≤ ((1000 : ℕ) : ℝ) ^ (-(((17 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((1000 : ℕ) : ℝ) ^ (-(((17 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((159/20000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_1000_19 :
    ((199/100000000 : ℚ) : ℝ) ≤ ((1000 : ℕ) : ℝ) ^ (-(((19 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((1000 : ℕ) : ℝ) ^ (-(((19 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((1/500000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_1000_20 :
    ((1/1000000 : ℚ) : ℝ) ≤ ((1000 : ℕ) : ℝ) ^ (-(((20 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((1000 : ℕ) : ℝ) ^ (-(((20 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((101/100000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_1000_21 :
    ((1/2000000 : ℚ) : ℝ) ≤ ((1000 : ℕ) : ℝ) ^ (-(((21 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((1000 : ℕ) : ℝ) ^ (-(((21 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((51/100000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_1000_24 :
    ((3/50000000 : ℚ) : ℝ) ≤ ((1000 : ℕ) : ℝ) ^ (-(((24 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((1000 : ℕ) : ℝ) ^ (-(((24 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((7/100000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_1000_25 :
    ((3/100000000 : ℚ) : ℝ) ≤ ((1000 : ℕ) : ℝ) ^ (-(((25 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((1000 : ℕ) : ℝ) ^ (-(((25 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((1/25000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_1000_26 :
    ((1/100000000 : ℚ) : ℝ) ≤ ((1000 : ℕ) : ℝ) ^ (-(((26 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((1000 : ℕ) : ℝ) ^ (-(((26 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((1/50000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_1000_27 :
    ((0 : ℚ) : ℝ) ≤ ((1000 : ℕ) : ℝ) ^ (-(((27 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((1000 : ℕ) : ℝ) ^ (-(((27 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((1/100000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_1000_29 :
    ((0 : ℚ) : ℝ) ≤ ((1000 : ℕ) : ℝ) ^ (-(((29 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((1000 : ℕ) : ℝ) ^ (-(((29 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((1/100000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_1000_31 :
    ((0 : ℚ) : ℝ) ≤ ((1000 : ℕ) : ℝ) ^ (-(((31 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((1000 : ℕ) : ℝ) ^ (-(((31 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((1/100000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_1000_34 :
    ((0 : ℚ) : ℝ) ≤ ((1000 : ℕ) : ℝ) ^ (-(((34 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((1000 : ℕ) : ℝ) ^ (-(((34 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((1/100000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_1000_37 :
    ((0 : ℚ) : ℝ) ≤ ((1000 : ℕ) : ℝ) ^ (-(((37 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((1000 : ℕ) : ℝ) ^ (-(((37 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((1/100000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.wbr_1000_5
#print axioms CriticalLinePhasor.DVP.wbr_1000_37
end AxiomAudit
