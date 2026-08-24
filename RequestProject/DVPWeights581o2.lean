import RequestProject.DVPLogBracket
import RequestProject.DVPWeights58

/-!
# Weight-bracket complement for rung-290.5 (the N = 500 boundary column)
-/

noncomputable section

namespace CriticalLinePhasor.DVP

theorem wbr_500_5 :
    ((447213/10000000 : ℚ) : ℝ) ≤ ((500 : ℕ) : ℝ) ^ (-(((5 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((500 : ℕ) : ℝ) ^ (-(((5 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((223607/5000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_500_6 :
    ((7507/312500 : ℚ) : ℝ) ≤ ((500 : ℕ) : ℝ) ^ (-(((6 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((500 : ℕ) : ℝ) ^ (-(((6 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((9609/400000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_500_7 :
    ((129039/10000000 : ℚ) : ℝ) ≤ ((500 : ℕ) : ℝ) ^ (-(((7 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((500 : ℕ) : ℝ) ^ (-(((7 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((1613/125000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_500_9 :
    ((2327/625000 : ℚ) : ℝ) ≤ ((500 : ℕ) : ℝ) ^ (-(((9 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((500 : ℕ) : ℝ) ^ (-(((9 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((37233/10000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_500_11 :
    ((10743/10000000 : ℚ) : ℝ) ≤ ((500 : ℕ) : ℝ) ^ (-(((11 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((500 : ℕ) : ℝ) ^ (-(((11 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((1343/1250000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_500_14 :
    ((333/2000000 : ℚ) : ℝ) ≤ ((500 : ℕ) : ℝ) ^ (-(((14 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((500 : ℕ) : ℝ) ^ (-(((14 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((833/5000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_500_15 :
    ((447/5000000 : ℚ) : ℝ) ≤ ((500 : ℕ) : ℝ) ^ (-(((15 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((500 : ℕ) : ℝ) ^ (-(((15 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((179/2000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_500_16 :
    ((3/62500 : ℚ) : ℝ) ≤ ((500 : ℕ) : ℝ) ^ (-(((16 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((500 : ℕ) : ℝ) ^ (-(((16 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((481/10000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_500_17 :
    ((129/5000000 : ℚ) : ℝ) ≤ ((500 : ℕ) : ℝ) ^ (-(((17 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((500 : ℕ) : ℝ) ^ (-(((17 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((259/10000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_500_19 :
    ((37/5000000 : ℚ) : ℝ) ≤ ((500 : ℕ) : ℝ) ^ (-(((19 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((500 : ℕ) : ℝ) ^ (-(((19 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((3/400000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_500_20 :
    ((1/250000 : ℚ) : ℝ) ≤ ((500 : ℕ) : ℝ) ^ (-(((20 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((500 : ℕ) : ℝ) ^ (-(((20 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((41/10000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_500_21 :
    ((21/10000000 : ℚ) : ℝ) ≤ ((500 : ℕ) : ℝ) ^ (-(((21 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((500 : ℕ) : ℝ) ^ (-(((21 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((11/5000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_500_24 :
    ((3/10000000 : ℚ) : ℝ) ≤ ((500 : ℕ) : ℝ) ^ (-(((24 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((500 : ℕ) : ℝ) ^ (-(((24 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((1/2500000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_500_25 :
    ((1/10000000 : ℚ) : ℝ) ≤ ((500 : ℕ) : ℝ) ^ (-(((25 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((500 : ℕ) : ℝ) ^ (-(((25 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((1/5000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_500_26 :
    ((0 : ℚ) : ℝ) ≤ ((500 : ℕ) : ℝ) ^ (-(((26 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((500 : ℕ) : ℝ) ^ (-(((26 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((1/10000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_500_27 :
    ((0 : ℚ) : ℝ) ≤ ((500 : ℕ) : ℝ) ^ (-(((27 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((500 : ℕ) : ℝ) ^ (-(((27 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((1/10000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_500_29 :
    ((0 : ℚ) : ℝ) ≤ ((500 : ℕ) : ℝ) ^ (-(((29 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((500 : ℕ) : ℝ) ^ (-(((29 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((1/10000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_500_31 :
    ((0 : ℚ) : ℝ) ≤ ((500 : ℕ) : ℝ) ^ (-(((31 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((500 : ℕ) : ℝ) ^ (-(((31 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((1/10000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_500_34 :
    ((0 : ℚ) : ℝ) ≤ ((500 : ℕ) : ℝ) ^ (-(((34 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((500 : ℕ) : ℝ) ^ (-(((34 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((1/10000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_500_37 :
    ((0 : ℚ) : ℝ) ≤ ((500 : ℕ) : ℝ) ^ (-(((37 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((500 : ℕ) : ℝ) ^ (-(((37 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((1/10000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.wbr_500_5
#print axioms CriticalLinePhasor.DVP.wbr_500_37
end AxiomAudit
