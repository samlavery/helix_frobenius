import RequestProject.MaassEntireHolo

/-!
# The Maass Petersson norm over the fundamental domain

The residue of the Eisenstein pairing at `s = 1` is the Petersson norm, so that norm has to be a
finite number before the pole split can be integrated.

It is, for the plainest of reasons: `maassWave_bounded` makes the density bounded on all of `ℍ`,
and `𝒟` has finite hyperbolic measure (`volume_fd_lt_top`).  Bounded against a finite measure —
no cusp estimate is needed at all, because the boundedness is global rather than asymptotic.

This is a place where the Maass case is *simpler* than the holomorphic one: `y^k‖f‖²` is only
bounded after the weight is accounted for, whereas `‖u‖²` is bounded outright.

**Scope.**  This is the `r = 2` rung.  Sato--Tate needs every rank; this is not a route to it.
-/

open MeasureTheory Complex UpperHalfPlane ModularGroup
open scoped Real MatrixGroups

namespace CriticalLinePhasor.Unfolding

open CriticalLinePhasor.ThreeDConverse

/-- **The Maass Petersson density is integrable over the fundamental domain.** -/
theorem maassP_integrableOn_fd (M : GenuineMaassCuspForm3D) :
    IntegrableOn (maassP M) ModularGroup.fd volume := by
  obtain ⟨C, hC0, hC⟩ := maassP_bounded M
  refine integrableOn_fd_of_bounded (continuous_maassP M) (C := C) fun z _ => ?_
  rw [Real.norm_of_nonneg (maassP_nonneg M z)]
  exact hC z

/-- The Petersson norm of a Maass form over the fundamental domain. -/
noncomputable def maassPetersson (M : GenuineMaassCuspForm3D) : ℝ :=
  ∫ z in ModularGroup.fd, maassP M z ∂(volume : Measure ℍ)

/-- The Petersson norm is nonnegative. -/
lemma maassPetersson_nonneg (M : GenuineMaassCuspForm3D) : 0 ≤ maassPetersson M :=
  setIntegral_nonneg measurableSet_fd fun z _ => maassP_nonneg M z

/-- The complex-valued density is integrable over the fundamental domain — the form the pairing's
pole split consumes. -/
theorem maassP_complex_integrableOn_fd (M : GenuineMaassCuspForm3D) :
    IntegrableOn (fun z : ℍ => ((maassP M z : ℝ) : ℂ)) ModularGroup.fd volume :=
  (maassP_integrableOn_fd M).ofReal

end CriticalLinePhasor.Unfolding

#print axioms CriticalLinePhasor.Unfolding.maassP_integrableOn_fd
#print axioms CriticalLinePhasor.Unfolding.maassPetersson_nonneg
#print axioms CriticalLinePhasor.Unfolding.maassP_complex_integrableOn_fd
