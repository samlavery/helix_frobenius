import RequestProject.MaassRSSwap

/-!
# The Eisenstein coset pairing continues meromorphically

Chaining the three compiled pieces:

* `lambda_eq_zeta_mul_cosetSum` — pointwise, `Λ_z(s)` is the archimedean factor times `ζ(2s)` times
  twice the coset sum;
* `maass_rs_swap` — the coset sum passes through the Petersson integral;
* `maass_pairing_pole_split_unconditional` — the `Λ`-pairing is entire minus two explicit poles.

Reading them in that order gives the coset pairing's continuation: it equals an entire function
minus `(1/s + 1/(1−s))·‖u‖²_Petersson`, all divided by the nonvanishing completed factor
`π^{-s}Γ(s)ζ(2s)`.  The pole at `s = 1` is genuine because `maassPetersson_pos`.

Nothing new is estimated here — the content is that three separately-proved identities compose,
which they do because all three are stated about the same integrand.

**Scope.**  This is the `r = 2` rung.  Sato--Tate needs every rank; this is not a route to it.
-/

open MeasureTheory Complex UpperHalfPlane ModularGroup
open scoped Real MatrixGroups

namespace CriticalLinePhasor.Unfolding

open CriticalLinePhasor.EpsteinTheta CriticalLinePhasor.ThreeDConverse

/-- **The coset pairing, continued.**  The archimedean factor times `ζ(2s)` times twice the
Petersson-paired coset sum equals an entire function minus two explicit simple poles. -/
theorem maass_cosetPairing_continuation (M : GenuineMaassCuspForm3D) {s : ℂ} (hs : 1 < s.re) :
    (((Real.pi : ℝ) : ℂ) ^ (-s) * Complex.Gamma s) *
        (riemannZeta (2 * s) *
          (2 * ∑' q : CosetQ, ∫ z in ModularGroup.fd,
            ((maassP M z : ℝ) : ℂ) *
              ((gram z ((rep q) 1 0, (rep q) 1 1) : ℝ) : ℂ) ^ (-s)
            ∂(volume : Measure ℍ))) =
      (∫ z in ModularGroup.fd,
        ((maassP M z : ℝ) : ℂ) * (generalFEPair z).Λ₀ s ∂(volume : Measure ℍ))
        - (1 / s + 1 / (1 - s)) * ((maassPetersson M : ℝ) : ℂ) := by
  rw [← maass_pairing_pole_split_unconditional M s, ← maass_rs_swap M hs]
  rw [← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_const_mul,
    ← MeasureTheory.integral_const_mul]
  refine setIntegral_congr_fun measurableSet_fd fun z _ => ?_
  rw [lambda_eq_zeta_mul_cosetSum z hs]
  ring

end CriticalLinePhasor.Unfolding

#print axioms CriticalLinePhasor.Unfolding.maass_cosetPairing_continuation
