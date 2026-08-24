import RequestProject.DVPLogBracket

/-!
# Weight-bracket complement for rung-81
-/

noncomputable section

namespace CriticalLinePhasor.DVP

theorem wbr_5_5 :
    ((894427/2000000 : ℚ) : ℝ) ≤ ((5 : ℕ) : ℝ) ^ (-(((5 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((5 : ℕ) : ℝ) ^ (-(((5 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((559017/1250000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.wbr_5_5
end AxiomAudit
