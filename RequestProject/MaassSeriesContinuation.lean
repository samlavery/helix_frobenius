import RequestProject.MaassCosetPairingContinuation
import RequestProject.MaassArchimedeanPositivity

/-!
# The Rankin--Selberg Dirichlet series inherits the continuation

The transfer.  `maass_cosetPairing_continuation` continues the pairing written in **Gram powers**;
`maass_rankinSeries_eq_pairing` expresses the arithmetic series through the pairing written in
**Eisenstein heights**.  `gram_rep_cpow_eq_im_cpow` says those are the same integrand, so the two
compose.

The result is that

  `π^{-σ}·Γ(σ)·ζ(2σ) · (∑ₙ|λₙ|²(n+1)^{-σ}) · A(σ)`

equals an entire function minus `(1/σ + 1/(1−σ))·‖u‖²_Petersson`.  Every factor on the left is
understood — `A(σ) > 0` (`archimedeanFactorReal_pos`), `ζ(2σ) ≠ 0` and `Γ(σ) ≠ 0`
(`archimedean_zeta_factor_ne_zero`) — so the arithmetic series carries the continuation, with a
genuine simple pole at `σ = 1` whose residue is the Petersson norm.

This is the analytic content of the `r = 2` Rankin--Selberg rung, for a Maass form, unconditional.

**Scope.**  `r = 2`.  Sato--Tate needs every rank; this is not a route to it.  What remains on this
rung is the edge argument turning the pole into `L(1, Sym²u) ≠ 0`.
-/

open MeasureTheory Complex UpperHalfPlane ModularGroup
open scoped Real MatrixGroups

namespace CriticalLinePhasor.Unfolding

open CriticalLinePhasor.EpsteinTheta CriticalLinePhasor.ThreeDConverse

/-- **The two pairings agree**: Gram powers at coset bottom rows are Eisenstein height powers. -/
theorem maass_pairing_gram_eq_height (M : GenuineMaassCuspForm3D) (s : ℂ) :
    (∑' q : CosetQ, ∫ z in ModularGroup.fd,
        ((maassP M z : ℝ) : ℂ) *
          ((gram z ((rep q) 1 0, (rep q) 1 1) : ℝ) : ℂ) ^ (-s) ∂(volume : Measure ℍ)) =
      ∑' q : CosetQ, ∫ z in ModularGroup.fd,
        ((maassP M z : ℝ) : ℂ) * (((rep q • z).im : ℝ) : ℂ) ^ s ∂(volume : Measure ℍ) := by
  refine tsum_congr fun q => setIntegral_congr_fun measurableSet_fd fun z _ => ?_
  rw [gram_rep_cpow_eq_im_cpow q z s]

/-- **The Rankin--Selberg Dirichlet series carries the continuation.**  Its product with the
completed archimedean factor is entire minus two explicit simple poles, the one at `σ = 1` having
the Petersson norm as residue. -/
theorem maass_rankinSeries_continuation (M : GenuineMaassCuspForm3D) {σ : ℝ}
    (hσ : (2 * (M.eigenData.E₀ + 2) : ℝ) + 1 < σ) :
    (((Real.pi : ℝ) : ℂ) ^ (-(σ : ℂ)) * Complex.Gamma (σ : ℂ)) *
        (riemannZeta (2 * (σ : ℂ)) *
          ((∑' n : ℕ, rankinSelbergTerm M (σ : ℂ) n) * archimedeanFactor M (σ : ℂ))) =
      (∫ z in ModularGroup.fd,
        ((maassP M z : ℝ) : ℂ) * (generalFEPair z).Λ₀ (σ : ℂ) ∂(volume : Measure ℍ))
        - (1 / (σ : ℂ) + 1 / (1 - (σ : ℂ))) * ((maassPetersson M : ℝ) : ℂ) := by
  have hE : (0:ℝ) ≤ 2 * (M.eigenData.E₀ + 2) := by positivity
  have hσ1 : 1 < σ := by linarith
  have hre : ((σ : ℂ)).re = σ := Complex.ofReal_re σ
  have hne : archimedeanFactor M (σ : ℂ) ≠ 0 := archimedeanFactor_ne_zero M hσ1
  have hser := maass_rankinSeries_eq_pairing M hσ
  rw [← maass_cosetPairing_continuation M (s := (σ : ℂ)) (by rw [hre]; exact hσ1),
    maass_pairing_gram_eq_height M (σ : ℂ)]
  rw [hser]
  field_simp

end CriticalLinePhasor.Unfolding

#print axioms CriticalLinePhasor.Unfolding.maass_pairing_gram_eq_height
#print axioms CriticalLinePhasor.Unfolding.maass_rankinSeries_continuation
