import RequestProject.CarrierThetaDirichletInverse
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The ladder transfer: smoothed cancellation descends through Dirichlet factorization

The reduction that makes the cancellation lemma attackable rung by rung.  The target
(`SmoothedCancellation`) is the weighted partial-sum bound with the weight explicit — the kernel
`h` *is* `ω_W`: the smoothed coefficient sum of the bank `a` at small height `1/x` grows at most
like `x^θ`.  The abelian rung holds sharp-cutoff (`CoefficientCancellation`), the GL(2) rung
holds with exponential saving (`HeckeCancellation`, kernel `e^{-2πy}`).

`smoothedCancellation_of_pairDilation` is the compiled descent: whenever a coefficient bank
factors as a Dirichlet convolution `a ⋆ b` — the shape of the tower's exact rung identity
`L(Sym^{m+1}) = F_m F_{-m} · L(Sym^{m-3}) · C_m^{-1}` — the smoothed cancellation for the
product bank follows from a bound on the *pair-dilation sum*: the `a`-dilation bank of the theta
of `b` (`positiveTheta_dilationKernel`, the compiled composition law).  So the tower lemma
reduces, rung by rung, to cancellation in the pair-dilation sums `∑_d f_m(d)·Θ(d·y)`, whose
coefficients are unit-angle products of the *base fiber's* Satake angles: a carrier-compiled
reduction with a fiber-side input — base-angle equidistribution — in place of tower-level
automorphy.  For a holomorphic base the fiber input is a cited theorem (Sato–Tate,
Barnet-Lamb--Geraghty--Harris--Taylor, proven independently of any tower construction); the
pair-dilation estimate itself is the named open work.  No RH/GRH assumed or proven.
-/

open scoped ArithmeticFunction

namespace CriticalLinePhasor.CarrierTheta

/-- **The smoothed cancellation target with explicit weight.**  The kernel `h` is the explicit
weight `ω_W`; the bound says the `h`-smoothed coefficient sums of `a` at height `1/x` grow at
most like `x^θ`. -/
def SmoothedCancellation (a : ArithmeticFunction ℂ) (h : ℝ → ℂ) (C θ : ℝ) : Prop :=
  ∀ x : ℝ, 1 ≤ x → ‖positiveTheta a h x⁻¹‖ ≤ C * x ^ θ

/-- **The ladder transfer.**  If the bank factors as a Dirichlet convolution `a ⋆ b`, the
smoothed cancellation for the product follows from the pair-dilation bound: the `a`-dilation
bank of the theta of `b`.  This is the compiled reduction of the tower cancellation lemma to
the pair-dilation estimate, one rung at a time. -/
theorem smoothedCancellation_of_pairDilation
    (a b : ArithmeticFunction ℂ) (h : ℝ → ℂ) (C θ : ℝ)
    (hsum : ∀ x : ℝ, 1 ≤ x → Summable fun p : ℕ+ × ℕ+ =>
      a p.1 * b p.2 * h (((p.1 : ℕ) * (p.2 : ℕ)) * x⁻¹))
    (hbound : ∀ x : ℝ, 1 ≤ x →
      ‖positiveTheta a (dilationKernel b h) x⁻¹‖ ≤ C * x ^ θ) :
    SmoothedCancellation (a * b) h C θ := by
  intro x hx
  rw [← positiveTheta_dilationKernel a b h x⁻¹ (hsum x hx)]
  exact hbound x hx

/-- Smoothed cancellation composes along a full factorization chain: a bank factoring through
`n` rungs needs only the `n` pair-dilation bounds. -/
theorem smoothedCancellation_of_triple
    (a b c : ArithmeticFunction ℂ) (h : ℝ → ℂ) (C θ : ℝ)
    (hsum₁ : ∀ x : ℝ, 1 ≤ x → Summable fun p : ℕ+ × ℕ+ =>
      a p.1 * (b * c) p.2 * h (((p.1 : ℕ) * (p.2 : ℕ)) * x⁻¹))
    (hbound : ∀ x : ℝ, 1 ≤ x →
      ‖positiveTheta a (dilationKernel (b * c) h) x⁻¹‖ ≤ C * x ^ θ) :
    SmoothedCancellation (a * b * c) h C θ := by
  have := smoothedCancellation_of_pairDilation a (b * c) h C θ hsum₁ hbound
  rwa [← mul_assoc] at this

end CriticalLinePhasor.CarrierTheta

#print axioms CriticalLinePhasor.CarrierTheta.smoothedCancellation_of_pairDilation
#print axioms CriticalLinePhasor.CarrierTheta.smoothedCancellation_of_triple
