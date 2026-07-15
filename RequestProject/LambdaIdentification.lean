import RequestProject.ReindexSum

/-!
# The completed Epstein kernel is the Gram Dirichlet series

The opening brick of the continuation step.  On `Re s > 1` the compiled abstract completion
`Λ_z` of the lattice bank — which continues to `ℂ ∖ {0,1}` with functional equation, at every
`z`, by items 82/86 — is identified term by term with the Gram Dirichlet series
(`lambda_eq_gram_series`):

  `Λ_z(s) = Γ(s) · π^{-s} · ∑'_{p≠0} gram(z,p)^{-s}`.

The engine is `hasSum_mellin` once more: the bank minus its DC term is the exponential series
over the nonzero lattice (`hasSum_nz_theta`), and the abstract `WeakFEPair.hasMellin`
identifies its Mellin transform with `Λ_z` on the half-plane.  Composed with the compiled
factorization (`gram_sum_factor`) and the Rankin–Selberg equation, this expresses the
completed Dirichlet series through an object whose analytic continuation in `s` is already
compiled pointwise in `z` — the input for continuing the unfolded integral.  No RH/GRH.
-/

open MeasureTheory Complex UpperHalfPlane ModularGroup
open scoped Real MatrixGroups

namespace CriticalLinePhasor.Unfolding

open CriticalLinePhasor.EpsteinTheta

/-- **The bank minus its DC term sums over the nonzero lattice.** -/
lemma hasSum_nz_theta (z : ℍ) {t : ℝ} (ht : 0 < t) :
    HasSum (fun p : NZ => Real.exp (-(π * t) * gram z p.1))
      (latticeTheta z t - 1) := by
  have hsummable := summable_latticeTheta_term z ht
  have hsub : Summable fun p : NZ => Real.exp (-(π * t) * gram z p.1) :=
    hsummable.subtype _
  have hval : ∑' p : NZ, Real.exp (-(π * t) * gram z p.1) =
      latticeTheta z t - 1 := by
    have hsplit := hsummable.tsum_eq_add_tsum_ite (0 : ℤ × ℤ)
    rw [gram_zero, mul_zero, Real.exp_zero] at hsplit
    have hcongr : ∀ p : NZ, Real.exp (-(π * t) * gram z p.1) =
        ite (p.1 = 0) 0 (Real.exp (-(π * t) * gram z p.1)) := by
      intro p
      rw [if_neg p.2]
    have hsupp : Function.support (fun p : ℤ × ℤ =>
        ite (p = 0) 0 (Real.exp (-(π * t) * gram z p))) ⊆
        Set.range (Subtype.val : NZ → ℤ × ℤ) := by
      intro p hp
      rw [Function.mem_support] at hp
      by_cases hz : p = 0
      · rw [if_pos hz] at hp
        exact absurd rfl hp
      · exact ⟨⟨p, hz⟩, rfl⟩
    have hie : ∑' p : NZ, Real.exp (-(π * t) * gram z p.1) =
        ∑' p : ℤ × ℤ, ite (p = 0) 0 (Real.exp (-(π * t) * gram z p)) := by
      rw [tsum_congr hcongr]
      exact Function.Injective.tsum_eq Subtype.val_injective hsupp
    rw [hie]
    have hlt : latticeTheta z t = 1 + ∑' p : ℤ × ℤ,
        ite (p = 0) 0 (Real.exp (-(π * t) * gram z p)) := by
      rw [latticeTheta]
      exact hsplit
    linarith
  rw [← hval]
  exact hsub.hasSum

/-- **The completed Epstein kernel is the Gram Dirichlet series** on `Re s > 1` — the
identification that hands the compiled continuation of `Λ_z` to the Rankin–Selberg
Dirichlet series. -/
theorem lambda_eq_gram_series (z : ℍ) {s : ℂ} (hs : 1 < s.re) :
    (generalFEPair z).Λ s =
      Complex.Gamma s * ((π : ℝ) : ℂ) ^ (-s) *
        ∑' p : NZ, ((gram z p.1 : ℝ) : ℂ) ^ (-s) := by
  have hk : (generalFEPair z).k < s.re := by
    show (1 : ℝ) < s.re
    exact hs
  have hM := (generalFEPair z).hasMellin hk
  have hMel : mellin (fun t => latticeThetaC z t - 1) s = (generalFEPair z).Λ s := hM.2
  have hp : ∀ p : NZ, (1 : ℂ) = 0 ∨ 0 < π * gram z p.1 := fun p =>
    Or.inr (by have := gram_pos z p.2; positivity)
  have hs0 : 0 < s.re := by linarith
  have hF : ∀ t ∈ Set.Ioi (0 : ℝ), HasSum (fun p : NZ =>
      (1 : ℂ) * Real.exp (-(π * gram z p.1) * t)) (latticeThetaC z t - 1) := by
    intro t ht
    have hreal := hasSum_nz_theta z (Set.mem_Ioi.mp ht)
    have hcast : HasSum
        (fun p : NZ => ((Real.exp (-(π * t) * gram z p.1) : ℝ) : ℂ))
        (((latticeTheta z t - 1 : ℝ)) : ℂ) := Complex.hasSum_ofReal.mpr hreal
    convert hcast using 1
    · funext p
      rw [one_mul, show -(π * gram z p.1) * t = -(π * t) * gram z p.1 by ring]
    · rw [latticeThetaC]
      push_cast
      ring
  have h_sum : Summable fun p : NZ => ‖(1 : ℂ)‖ / (π * gram z p.1) ^ s.re := by
    have h1 := (summable_gram_rpow z (σ := s.re) hs).mul_left ((π : ℝ) ^ (-s.re))
    refine h1.congr fun p => ?_
    have hg := gram_pos z p.2
    rw [norm_one, one_div, ← Real.mul_rpow Real.pi_pos.le hg.le,
      Real.rpow_neg (by positivity)]
  have hmellin := hasSum_mellin hp hs0 hF h_sum
  rw [← hMel, ← hmellin.tsum_eq, mul_assoc, ← tsum_mul_left, ← tsum_mul_left]
  refine tsum_congr fun p => ?_
  have hg := gram_pos z p.2
  rw [mul_one, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg Real.pi_pos.le hg.le,
    Complex.cpow_neg, Complex.cpow_neg, div_eq_mul_inv, mul_inv]

end CriticalLinePhasor.Unfolding

#print axioms CriticalLinePhasor.Unfolding.hasSum_nz_theta
#print axioms CriticalLinePhasor.Unfolding.lambda_eq_gram_series
