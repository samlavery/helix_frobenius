import RequestProject.DVPLogBracket

/-!
# Weight-bracket complement for rung-74
-/

noncomputable section

namespace CriticalLinePhasor.DVP

theorem wbr_4_5 :
    ((1/2 : ℚ) : ℝ) ≤ ((4 : ℕ) : ℝ) ^ (-(((5 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((4 : ℕ) : ℝ) ^ (-(((5 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((5000001/10000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_8_5 :
    ((3535533/10000000 : ℚ) : ℝ) ≤ ((8 : ℕ) : ℝ) ^ (-(((5 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((8 : ℕ) : ℝ) ^ (-(((5 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((1767767/5000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.wbr_4_5
end AxiomAudit
