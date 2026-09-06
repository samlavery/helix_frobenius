import RequestProject.JKernelSignLaw

/-!
# Horizontal phase in the paired theta kernel

Write J(d,s) = s K(|(s+d)/2|) K(|(s-d)/2|). For y,s > 0,
the vertical pairing B(d,y,s) = J(d,s)e^(-ys) + J(d,-s)e^(ys)
is strictly negative. At every nonzero horizontal frequency x, choosing
d = pi/x makes cos(xd) B(d,y,s) strictly positive. Thus the pointwise
vertical sign cannot be multiplied by the horizontal cosine uniformly.
This calculation does not determine the sign of the integrated pairing.

Searches:
`rg -n 'JKernel|jKernel|kernel.*nonpos|numerator.*nonpos' RequestProject --glob '*.lean'`
`rg -n 'riemannXiKernel_pos|sinh_pos|cos_pi|mul_pos_of_neg_of_neg' RequestProject/JKernelSignLaw.lean RequestProject/ThetaWronskianSuzukiGram.lean .lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Trigonometric --glob '*.lean'`
Semantic searches: LeanSearch, double integral derivative Fourier cosine
transform multiplied by complex conjugate positivity; Loogle, integral_mul.
-/

noncomputable section

namespace CriticalLinePhasor.JKernel

open ThetaWronskianSuzukiGram

-- Expectation-free step: retain the horizontal cosine factor in the
-- vertically paired kernel. Test its sign at a half-turn explicitly.
-- Strategy A: multiply jKernel_pairing_nonpos by a nonnegative cosine.
-- Strategy B: rewrite jKernel_pairing_eq and use strict positivity of K.
-- The second calculation below exhibits the first strategy's excluded case.

theorem pairing_strictly_neg {y s : ℝ} (hy : 0 < y) (hs : 0 < s) (d : ℝ) :
    jKernel d s * Real.exp (-(y * s)) + jKernel d (-s) * Real.exp (y * s) < 0 := by
  rw [jKernel_pairing_eq]
  have hk (u : ℝ) : 0 < phiEven u := riemannXiKernel_pos (abs_nonneg u)
  have hj : 0 < jKernel d s := mul_pos (mul_pos hs (hk _)) (hk _)
  have hh : 0 < Real.sinh (y * s) := Real.sinh_pos_iff.mpr (mul_pos hy hs)
  exact neg_neg_of_pos (mul_pos (mul_pos (by norm_num) hj) hh)

theorem horizontal_half_turn_reverses_sign {y s : ℝ} (hy : 0 < y) (hs : 0 < s) :
    0 < Real.cos Real.pi *
      (jKernel 1 s * Real.exp (-(y * s)) + jKernel 1 (-s) * Real.exp (y * s)) := by
  rw [Real.cos_pi, neg_one_mul]
  exact neg_pos.mpr (pairing_strictly_neg hy hs 1)

theorem horizontal_phase_has_positive_point {x y s : ℝ}
    (hx : x ≠ 0) (hy : 0 < y) (hs : 0 < s) :
    ∃ d : ℝ, 0 < Real.cos (x * d) *
      (jKernel d s * Real.exp (-(y * s)) + jKernel d (-s) * Real.exp (y * s)) := by
  refine ⟨Real.pi / x, ?_⟩
  have hphase : x * (Real.pi / x) = Real.pi := by field_simp
  rw [hphase, Real.cos_pi, neg_one_mul]
  exact neg_pos.mpr (pairing_strictly_neg hy hs _)

end CriticalLinePhasor.JKernel

#print axioms CriticalLinePhasor.JKernel.pairing_strictly_neg
#print axioms CriticalLinePhasor.JKernel.horizontal_half_turn_reverses_sign
#print axioms CriticalLinePhasor.JKernel.horizontal_phase_has_positive_point
