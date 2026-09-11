import Mathlib
open Complex
#print RiemannHypothesis
#check (riemannZeta (1 + 8 * I) : ℂ)
example : riemannZeta (1 + 8 * I) ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by simp)
