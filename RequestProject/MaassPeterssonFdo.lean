import RequestProject.MaassPeterssonAeZero
import RequestProject.BoundaryNull

/-!
# Transferring the vanishing to the open fundamental domain

`maassP_ae_zero_of_petersson_zero` gives a.e.-vanishing on the closed domain `𝒟`.  The topological
upgrade wants an *open* set to work on, and `𝒟ᵒ ⊆ 𝒟` (Mathlib's `fdo_subset_fd`) transfers the
a.e. statement there for free — restriction to a subset weakens an a.e. statement.

Nothing is lost by the move: `BoundaryNull.fd_boundary_null` says `𝒟 \ 𝒟ᵒ` is null, so the closed
and open domains carry the same measure-theoretic information.  The two facts are complementary —
`fdo_subset_fd` moves the statement inward, `fd_boundary_null` says the move costs nothing.

**Scope.**  The remaining step — a continuous function vanishing a.e. on a nonempty open set
vanishes on it — needs the hyperbolic measure to be positive on nonempty opens
(`IsOpenPosMeasure`), which is not established here.

This is the `r = 2` rung.  Sato--Tate needs every rank; this is not a route to it.
-/

open MeasureTheory UpperHalfPlane ModularGroup
open scoped Real MatrixGroups

namespace CriticalLinePhasor.Unfolding

open CriticalLinePhasor.ThreeDConverse

/-- **The vanishing transfers to the open fundamental domain.** -/
theorem maassP_ae_zero_on_fdo (M : GenuineMaassCuspForm3D)
    (h : maassPetersson M = 0) :
    maassP M =ᵐ[(volume : Measure ℍ).restrict ModularGroup.fdo] 0 :=
  ae_restrict_of_ae_restrict_of_subset ModularGroup.fdo_subset_fd
    (maassP_ae_zero_of_petersson_zero M h)

/-- The closed and open domains carry the same measure — the boundary is null. -/
theorem volume_fd_eq_volume_fdo :
    (volume : Measure ℍ) ModularGroup.fd = (volume : Measure ℍ) ModularGroup.fdo := by
  refine le_antisymm ?_ (measure_mono ModularGroup.fdo_subset_fd)
  have hcov : ModularGroup.fd ⊆
      ModularGroup.fdo ∪ (ModularGroup.fd \ ModularGroup.fdo) := by
    intro z hz
    by_cases h : z ∈ ModularGroup.fdo
    · exact Or.inl h
    · exact Or.inr ⟨hz, h⟩
  calc (volume : Measure ℍ) ModularGroup.fd
      ≤ (volume : Measure ℍ) ModularGroup.fdo +
        (volume : Measure ℍ) (ModularGroup.fd \ ModularGroup.fdo) :=
        le_trans (measure_mono hcov) (measure_union_le _ _)
    _ = (volume : Measure ℍ) ModularGroup.fdo := by
        rw [fd_boundary_null, add_zero]

end CriticalLinePhasor.Unfolding

#print axioms CriticalLinePhasor.Unfolding.maassP_ae_zero_on_fdo
