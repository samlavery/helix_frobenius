import RequestProject.DVPLogBracket

/-!
# Weight-bracket complement for rung-63 (sign pattern differs from t=58)
-/

noncomputable section

namespace CriticalLinePhasor.DVP

theorem wbr_2_20 :
    ((1/4 : ℚ) : ℝ) ≤ ((2 : ℕ) : ℝ) ^ (-(((20 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((2 : ℕ) : ℝ) ^ (-(((20 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((2500001/10000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_6_20 :
    ((277777/10000000 : ℚ) : ℝ) ≤ ((6 : ℕ) : ℝ) ^ (-(((20 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((6 : ℕ) : ℝ) ^ (-(((20 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((138889/5000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_7_5 :
    ((944911/2500000 : ℚ) : ℝ) ≤ ((7 : ℕ) : ℝ) ^ (-(((5 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((7 : ℕ) : ℝ) ^ (-(((5 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((755929/2000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_9_20 :
    ((1929/156250 : ℚ) : ℝ) ≤ ((9 : ℕ) : ℝ) ^ (-(((20 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((9 : ℕ) : ℝ) ^ (-(((20 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((123457/10000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_10_20 :
    ((99999/10000000 : ℚ) : ℝ) ≤ ((10 : ℕ) : ℝ) ^ (-(((20 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((10 : ℕ) : ℝ) ^ (-(((20 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((1/100 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.wbr_2_20
end AxiomAudit
