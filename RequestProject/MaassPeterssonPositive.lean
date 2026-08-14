import RequestProject.MaassPeterssonNorm

/-!
# Vanishing on the fundamental domain forces vanishing everywhere

Toward positivity of the Petersson norm, which is what makes the pole of the Eisenstein pairing at
`s = 1` genuine rather than removable.

The spreading step is immediate from the two facts that define the situation: every point of `ℍ` is
`SL(2,ℤ)`-equivalent to a point of `𝒟` (`exists_smul_mem_fd`) and the Maass wave is invariant
(`level_one_invariant`).  So the density cannot vanish on `𝒟` without vanishing on the whole
half-plane — and `wave_ne_zero` forbids that.

This is the same argument as `maassWave_bounded_of_bounded_on_fd` from the start of this campaign,
run with "is zero" in place of "is bounded by `C`": the fundamental domain sees everything, because
invariance means there is nothing outside it to see.

**Scope.**  The measure-theoretic step — that a continuous nonnegative density with zero integral
over `𝒟` vanishes *pointwise* on `𝒟` — is not proved here, so `0 < maassPetersson` does not follow
yet.

This is the `r = 2` rung.  Sato--Tate needs every rank; this is not a route to it.
-/

open MeasureTheory UpperHalfPlane ModularGroup
open scoped Real MatrixGroups

namespace CriticalLinePhasor.Unfolding

open CriticalLinePhasor.ThreeDConverse

/-- **Vanishing on `𝒟` spreads to all of `ℍ`.** -/
theorem maassWave_eq_zero_of_eq_zero_on_fd (M : GenuineMaassCuspForm3D)
    (h : ∀ z ∈ ModularGroup.fd, maassWave M.eigenData M.radialKernel z = 0) :
    ∀ z : UpperHalfPlane, maassWave M.eigenData M.radialKernel z = 0 := by
  intro z
  obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd z
  have hb := h (g • z) hg
  rwa [M.level_one_invariant g z] at hb

/-- **The density cannot vanish identically on `𝒟`.**  The wave is nonzero, and `𝒟` sees
everything. -/
theorem maassP_not_all_zero_on_fd (M : GenuineMaassCuspForm3D) :
    ¬ (∀ z ∈ ModularGroup.fd, maassP M z = 0) := by
  intro hzero
  refine M.wave_ne_zero (funext fun z => ?_)
  refine maassWave_eq_zero_of_eq_zero_on_fd M (fun w hw => ?_) z
  have := hzero w hw
  rw [maassP, pow_eq_zero_iff (by norm_num)] at this
  exact norm_eq_zero.mp this

end CriticalLinePhasor.Unfolding

#print axioms CriticalLinePhasor.Unfolding.maassWave_eq_zero_of_eq_zero_on_fd
#print axioms CriticalLinePhasor.Unfolding.maassP_not_all_zero_on_fd
