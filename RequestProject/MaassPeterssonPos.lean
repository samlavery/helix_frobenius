import RequestProject.MaassPeterssonFdoZero
import RequestProject.UnfoldingIdentity

/-!
# The Petersson norm is positive

The residue of the Eisenstein pairing at `s = 1` is the Petersson norm, so the pole is genuine
exactly when that norm is nonzero.  It is.

The argument closes a gap that looked topological but is measure-theoretic.  Suppose the norm
vanishes.  Then the density vanishes on the *open* domain (`maassP_eq_zero_on_fdo`), so the
nonvanishing set `U` — open, and nonempty because the wave is nonzero — can only meet the closed
domain in its boundary.  Transporting by invariance, `U` is covered by the `SL(2,ℤ)`-translates of
that boundary: countably many null sets.  So `U` is null, contradicting that a nonempty open set has
positive measure (`upperHalfPlane_isOpenPosMeasure`).

Three compiled facts do the work and none of them is an estimate: `fd_boundary_null` (the boundary
is null), `SMulInvariantMeasure SL(2,ℤ) ℍ volume` (translates preserve it), and the countability of
the group.  The boundary is invisible to the measure, and a countable family of invisible sets
cannot cover something visible.

**Scope.**  This is the `r = 2` rung.  Sato--Tate needs every rank; this is not a route to it.
-/

open MeasureTheory UpperHalfPlane ModularGroup
open scoped Real MatrixGroups Pointwise

namespace CriticalLinePhasor.Unfolding

open CriticalLinePhasor.ThreeDConverse

/-- **The Petersson norm of a Maass cusp form is positive.** -/
theorem maassPetersson_pos (M : GenuineMaassCuspForm3D) : 0 < maassPetersson M := by
  haveI hmc : Countable (Matrix (Fin 2) (Fin 2) ℤ) :=
    Countable.of_equiv (Fin 2 → Fin 2 → ℤ) Matrix.of
  haveI : Countable SL(2, ℤ) := Subtype.countable
  rcases lt_or_eq_of_le (maassPetersson_nonneg M) with h | h
  · exact h
  exfalso
  have hfdo := maassP_eq_zero_on_fdo M h.symm
  set U : Set ℍ := {z : ℍ | maassP M z ≠ 0} with hUdef
  have hUopen : IsOpen U := isOpen_compl_singleton.preimage (continuous_maassP M)
  have hUne : U.Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    refine M.wave_ne_zero (funext fun z => ?_)
    have hz : maassP M z = 0 := by
      by_contra hc
      exact Set.eq_empty_iff_forall_notMem.mp hemp z hc
    rw [maassP, pow_eq_zero_iff (by norm_num)] at hz
    exact norm_eq_zero.mp hz
  -- `U` is covered by the translates of the (null) boundary
  have hcov : U ⊆ ⋃ g : SL(2, ℤ), (g • (ModularGroup.fd \ ModularGroup.fdo)) := by
    intro z hz
    obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd z
    have hgU : maassP M (g • z) ≠ 0 := by
      rw [maassP, M.level_one_invariant g z]
      exact hz
    have hgnot : g • z ∉ ModularGroup.fdo := fun hc => hgU (hfdo _ hc)
    exact Set.mem_iUnion.mpr ⟨g⁻¹, ⟨g • z, ⟨hg, hgnot⟩, inv_smul_smul g z⟩⟩
  have hnull : (volume : Measure ℍ) U = 0 := by
    refine measure_mono_null hcov (measure_iUnion_null fun g => ?_)
    have himg : (g • (ModularGroup.fd \ ModularGroup.fdo)) =
        (fun z : ℍ => g⁻¹ • z) ⁻¹' (ModularGroup.fd \ ModularGroup.fdo) := by
      ext z
      simp [Set.mem_smul_set_iff_inv_smul_mem]
    rw [himg, measure_preimage_smul]
    exact fd_boundary_null
  exact (hUopen.measure_pos volume hUne).ne' hnull

end CriticalLinePhasor.Unfolding

#print axioms CriticalLinePhasor.Unfolding.maassPetersson_pos
