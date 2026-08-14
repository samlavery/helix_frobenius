import RequestProject.MaassCoeffSummable

/-!
# The Mellin substitution: the arithmetic factors out

The step that turns the Maass Rankin--Selberg strip integral into a Dirichlet series.

After Parseval the strip integrand is `∑ₙ |λₙ|²·‖K((n+1)y)‖²` against `y^{s-1} dy`, so each term is
a Mellin transform of a *dilate* of the fixed function `‖K‖²`.  Mathlib's `mellin_comp_mul_left`
says a dilation by `a > 0` costs exactly `a^{-s}`, so the `n`-th term is

  `|λₙ|² · (n+1)^{-s} · A(s)`,   `A(s) = mellin ‖K‖² s`,

with `A` a single archimedean integral independent of the arithmetic.  Summing, the arithmetic
appears exactly as the Rankin--Selberg Dirichlet series `∑ₙ |λₙ|²(n+1)^{-s}` multiplied by `A(s)`.

**This is what makes the continuation argument work without evaluating any Bessel integral.**  `A(s)`
never has to be computed in closed form: the left-hand side inherits meromorphic continuation from
the Eisenstein side (`RSPoleStructure.lambda_pole_split`), so the Dirichlet series inherits it too
wherever `A(s) ≠ 0`.

Scope: the termwise identity is proven here.  Interchanging the sum with the Mellin integral, and
the nonvanishing of `A`, are not.
-/

open Complex MeasureTheory

namespace CriticalLinePhasor.ThreeDConverse

/-- The archimedean factor: the Mellin transform of the squared radial kernel.  It carries no
arithmetic. -/
noncomputable def archimedeanFactor (M : GenuineMaassCuspForm3D) (s : ℂ) : ℂ :=
  mellin (fun t : ℝ => ((‖M.radialKernel t‖ ^ 2 : ℝ) : ℂ)) s

/-- The `n`-th term of the Rankin--Selberg Dirichlet series. -/
noncomputable def rankinSelbergTerm (M : GenuineMaassCuspForm3D) (s : ℂ) (n : ℕ) : ℂ :=
  ((‖M.eigenData.lam (n + 1)‖ ^ 2 : ℝ) : ℂ) * (((n : ℝ) + 1 : ℂ)) ^ (-s)

/-- **Dilation costs exactly `(n+1)^{-s}`.**  The `n`-th Fourier mode contributes the fixed
archimedean factor scaled by the arithmetic frequency. -/
theorem mellin_kernelSq_scaled (M : GenuineMaassCuspForm3D) (n : ℕ) (s : ℂ) :
    mellin (fun y : ℝ => ((‖M.radialKernel (((n : ℝ) + 1) * y)‖ ^ 2 : ℝ) : ℂ)) s =
      (((n : ℝ) + 1 : ℂ)) ^ (-s) • archimedeanFactor M s := by
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h := mellin_comp_mul_left
    (fun t : ℝ => ((‖M.radialKernel t‖ ^ 2 : ℝ) : ℂ)) s hpos
  rw [archimedeanFactor]
  simpa using h

/-- **The arithmetic factors out of the `n`-th term.**  Each Fourier mode's Mellin transform is its
Rankin--Selberg coefficient times one fixed archimedean integral. -/
theorem mellin_maass_term (M : GenuineMaassCuspForm3D) (n : ℕ) (s : ℂ) :
    mellin (fun y : ℝ =>
      ((‖M.eigenData.lam (n + 1)‖ ^ 2 * ‖M.radialKernel (((n : ℝ) + 1) * y)‖ ^ 2 : ℝ) : ℂ)) s =
      rankinSelbergTerm M s n * archimedeanFactor M s := by
  have hconst : (fun y : ℝ =>
      ((‖M.eigenData.lam (n + 1)‖ ^ 2 * ‖M.radialKernel (((n : ℝ) + 1) * y)‖ ^ 2 : ℝ) : ℂ)) =
      fun y : ℝ => ((‖M.eigenData.lam (n + 1)‖ ^ 2 : ℝ) : ℂ) •
        ((‖M.radialKernel (((n : ℝ) + 1) * y)‖ ^ 2 : ℝ) : ℂ) := by
    funext y
    push_cast
    ring
  rw [hconst, mellin_const_smul, mellin_kernelSq_scaled M n s, rankinSelbergTerm,
    smul_eq_mul, smul_eq_mul]
  ring

end CriticalLinePhasor.ThreeDConverse

#print axioms CriticalLinePhasor.ThreeDConverse.mellin_kernelSq_scaled
#print axioms CriticalLinePhasor.ThreeDConverse.mellin_maass_term
