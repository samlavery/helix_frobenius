import RequestProject.RSSwap

/-!
# The master equation: the Petersson–Λ pairing is the completed Rankin–Selberg series

The composition of the entire compiled chain.  For `Re s > 2`:

  `∫_𝒟 P(z) · Λ_z(s) dμ  =  Γ(s)·π^{-s} · 2ζ(2s) · Γ(s+k-1) · ∑' ‖a_n‖²/(4πn)^{s+k-1}`

(`rs_master`) — pointwise the compiled `Λ_z` is the Gram Dirichlet series
(`lambda_eq_gram_series`), which factors through the coset sum (`gram_sum_factor`); the coset
sum passes through the Petersson integral (`rs_swap`); and the resulting pairing is the
Rankin–Selberg equation (`rankin_selberg_equation_gram`).  The left side is built from
`Λ_z` — compiled to continue to `ℂ ∖ {0,1}` with functional equation at every `z` — so this
equation is the vehicle carrying the completed Rankin–Selberg Dirichlet series past its
convergence half-plane: the continuation step differentiates the left side under the
integral.  No RH/GRH.
-/

open MeasureTheory Complex UpperHalfPlane ModularGroup
open scoped Real MatrixGroups

namespace CriticalLinePhasor.Unfolding

open CriticalLinePhasor.HeckeSupBound CriticalLinePhasor.EpsteinTheta

variable {k : ℤ}

/-- **The master equation**: the Petersson pairing against the compiled Epstein completion
equals the completed Rankin–Selberg Dirichlet series with explicit `Γζ`-factors, on
`Re s > 2`. -/
theorem rs_master (f : CuspForm 𝒮ℒ k) (hk : 0 ≤ k) {s : ℂ} (hs : 2 < s.re) :
    ∫ z in ModularGroup.fd, ((P k f z : ℝ) : ℂ) * (generalFEPair z).Λ s ∂volume =
      Complex.Gamma s * ((π : ℝ) : ℂ) ^ (-s) * (2 * riemannZeta (2 * s)) *
        (Complex.Gamma (s + k - 1) * ∑' n : ℕ,
          ((‖(qExpansion 1 f).coeff n‖ ^ 2 : ℝ) : ℂ) /
            ((4 * π * n : ℝ) : ℂ) ^ (s + k - 1)) := by
  have hs1 : 1 < s.re := by linarith
  have hpoint : ∀ z : ℍ, ((P k f z : ℝ) : ℂ) * (generalFEPair z).Λ s =
      (Complex.Gamma s * ((π : ℝ) : ℂ) ^ (-s) * (2 * riemannZeta (2 * s))) *
        (((P k f z : ℝ) : ℂ) * ∑' q : CosetQ,
          ((gram z ((rep q).1 1 0, (rep q).1 1 1) : ℝ) : ℂ) ^ (-s)) := by
    intro z
    rw [lambda_eq_gram_series z hs1, gram_sum_factor z hs1]
    ring
  rw [setIntegral_congr_fun measurableSet_fd fun z _ => hpoint z,
    MeasureTheory.integral_const_mul, rs_swap f hk hs1,
    ← rankin_selberg_equation_gram f hk hs]

end CriticalLinePhasor.Unfolding

#print axioms CriticalLinePhasor.Unfolding.rs_master
