import RequestProject.MaassPeterssonPositive

/-!
# A vanishing Petersson norm forces the density to vanish almost everywhere

The measure-theoretic half of Petersson positivity.  The density is continuous, nonnegative and
integrable over `𝒟` (`maassP_integrableOn_fd`), so a zero integral forces it to vanish almost
everywhere there — that direction needs nothing but nonnegativity.

What is *not* here is the topological half: upgrading "almost everywhere on `𝒟`" to "everywhere on
`𝒟`", which is what `maassP_not_all_zero_on_fd` would then contradict.  The tool for it is the
corpus's `BoundaryNull.fd_boundary_null` (the boundary of `𝒟` is null), so a.e.-vanishing on `𝒟`
is a.e.-vanishing on the *interior*, and a continuous function vanishing a.e. on a nonempty open
set vanishes on it identically.  Spreading from the interior back to all of `ℍ` then needs the
translates of `interior 𝒟` to be dense — a countable union of null closed boundaries has empty
interior.  That chain is not built here.

**Scope.**  This is the `r = 2` rung.  Sato--Tate needs every rank; this is not a route to it.
-/

open MeasureTheory UpperHalfPlane ModularGroup
open scoped Real MatrixGroups

namespace CriticalLinePhasor.Unfolding

open CriticalLinePhasor.ThreeDConverse

/-- **A zero Petersson norm forces the density to vanish a.e. on `𝒟`.** -/
theorem maassP_ae_zero_of_petersson_zero (M : GenuineMaassCuspForm3D)
    (h : maassPetersson M = 0) :
    maassP M =ᵐ[(volume : Measure ℍ).restrict ModularGroup.fd] 0 := by
  have hnn : (0 : ℍ → ℝ) ≤ maassP M := fun z => maassP_nonneg M z
  exact (integral_eq_zero_iff_of_nonneg hnn (maassP_integrableOn_fd M)).mp h

/-- **The Petersson norm is zero only if the density is a.e. zero** — stated as the contrapositive
the positivity argument consumes. -/
theorem maassPetersson_pos_of_not_ae_zero (M : GenuineMaassCuspForm3D)
    (h : ¬ (maassP M =ᵐ[(volume : Measure ℍ).restrict ModularGroup.fd] 0)) :
    0 < maassPetersson M := by
  rcases lt_or_eq_of_le (maassPetersson_nonneg M) with hlt | heq
  · exact hlt
  · exact absurd (maassP_ae_zero_of_petersson_zero M heq.symm) h

end CriticalLinePhasor.Unfolding

#print axioms CriticalLinePhasor.Unfolding.maassP_ae_zero_of_petersson_zero
#print axioms CriticalLinePhasor.Unfolding.maassPetersson_pos_of_not_ae_zero
