import RequestProject.MaassPeterssonPos
import RequestProject.MaassEntireHolo

/-!
# The Eisenstein pairing's pole split

Integrating `lambda_pole_split` against the Maass density.  Pointwise, `Λ_z = Λ₀_z − 1/s − 1/(1−s)`
with `Λ₀` entire, so the pairing splits as

  `∫_𝒟 ‖u‖²·Λ_z(s) = ∫_𝒟 ‖u‖²·Λ₀_z(s) − (1/s + 1/(1−s))·‖u‖²_Petersson`,

the entire part plus two explicit simple poles whose common residue coefficient is the Petersson
norm — which `maassPetersson_pos` shows is **nonzero**, so the poles are genuine.

The `s`-independent part of this is already settled: `maass_entirePart_differentiable` says the
first term is entire, and `maassPetersson_pos` says the coefficient does not vanish.

**Named obligation.**  Splitting the integral needs the entire part to be *integrable* at the fixed
`s`, which is stated here as the explicit hypothesis `hint`.  That fact is available inside
`rs_entirePart_differentiable`'s proof (the dominating function `bound` is `s`-free, and
`lambda0_bound_on_fd` bounds `‖Λ₀‖` on `𝒟`), but it is not exposed as a lemma in the corpus, so it
is carried here rather than assumed silently.  Discharging it is a matter of factoring that
dominating bound out of the existing proof.

**Scope.**  This is the `r = 2` rung.  Sato--Tate needs every rank; this is not a route to it.
-/

open MeasureTheory Complex UpperHalfPlane ModularGroup
open scoped Real MatrixGroups

namespace CriticalLinePhasor.Unfolding

open CriticalLinePhasor.EpsteinTheta CriticalLinePhasor.ThreeDConverse

/-- **The pairing splits into an entire part and two explicit simple poles.** -/
theorem maass_pairing_pole_split (M : GenuineMaassCuspForm3D) (s : ℂ)
    (hint : IntegrableOn
      (fun z : ℍ => ((maassP M z : ℝ) : ℂ) * (generalFEPair z).Λ₀ s)
      ModularGroup.fd volume) :
    (∫ z in ModularGroup.fd,
        ((maassP M z : ℝ) : ℂ) * (generalFEPair z).Λ s ∂(volume : Measure ℍ)) =
      (∫ z in ModularGroup.fd,
        ((maassP M z : ℝ) : ℂ) * (generalFEPair z).Λ₀ s ∂(volume : Measure ℍ))
        - (1 / s + 1 / (1 - s)) * ((maassPetersson M : ℝ) : ℂ) := by
  have hconst : IntegrableOn
      (fun z : ℍ => (1 / s + 1 / (1 - s)) * ((maassP M z : ℝ) : ℂ))
      ModularGroup.fd volume :=
    (maassP_complex_integrableOn_fd M).const_mul _
  have hsplit : ∀ z : ℍ,
      ((maassP M z : ℝ) : ℂ) * (generalFEPair z).Λ s =
        ((maassP M z : ℝ) : ℂ) * (generalFEPair z).Λ₀ s
          - (1 / s + 1 / (1 - s)) * ((maassP M z : ℝ) : ℂ) := by
    intro z
    rw [lambda_pole_split z s]
    ring
  rw [setIntegral_congr_fun measurableSet_fd fun z _ => hsplit z,
    integral_sub hint hconst, MeasureTheory.integral_const_mul]
  congr 1
  congr 1
  rw [maassPetersson, ← integral_complex_ofReal]

end CriticalLinePhasor.Unfolding

#print axioms CriticalLinePhasor.Unfolding.maass_pairing_pole_split
