import Mathlib

/-!
# Holomorphy on the closed half-plane reduces to a neighborhood of the line

Last field of the rank-uniform analytic interface.  `LocalAnalyticInput3D` asks for a candidate
holomorphic on an open set containing all of `{Re s ≥ 1}`.  But the interior of that half-plane is
not a hypothesis: a Dirichlet series is holomorphic throughout its half-plane of convergence, and
the candidate is required to *agree* with it there.  So the only place a genuine extension is
needed is across the line itself.

The glue is elementary and purely local.  If `G` is holomorphic on an open `U ⊇ {Re s = 1}` and
agrees with `F` where they overlap, then the piecewise function `F` on `{Re s > 1}` and `G`
elsewhere is holomorphic on `U ∪ {Re s > 1}`, an open set containing `{Re s ≥ 1}` — because
differentiability is a local property and each point of the union has a neighborhood on which the
piecewise function equals one of the two pieces outright.

Consequence: the rank-uniform input is not "holomorphic on a half-plane, non-vanishing on a
half-plane, with two growth bounds."  It is "extends holomorphically across the line" — plus, by
`CPSEdgeBoundsFromPole3D`, one point of non-vanishing and a simple pole for the pair bank.  That is
the sharpest honest statement of what is missing, and it is exactly automorphy of the symmetric
powers.

**Scope.**  This is a complex-analysis interface result.  It supplies no arithmetic.
-/

open Complex Filter Topology

namespace CriticalLinePhasor.ThreeDConverse

open scoped Classical

/-- The half-plane `Re s > 1` is open. -/
lemma isOpen_one_lt_re : IsOpen {s : ℂ | 1 < s.re} :=
  isOpen_lt continuous_const Complex.continuous_re

/-- **A neighborhood of the line suffices.**  Holomorphy on an open set containing the closed
half-plane follows from holomorphy on the convergence half-plane — which a Dirichlet series has for
free — together with a holomorphic extension across the line. -/
theorem exists_halfplane_extension_of_line_neighborhood
    {F G : ℂ → ℂ} {U : Set ℂ}
    (hF : DifferentiableOn ℂ F {s : ℂ | 1 < s.re})
    (hU : IsOpen U) (hUline : {s : ℂ | s.re = 1} ⊆ U)
    (hG : DifferentiableOn ℂ G U)
    (hGF : Set.EqOn G F (U ∩ {s : ℂ | 1 < s.re})) :
    ∃ (cand : ℂ → ℂ) (D : Set ℂ), IsOpen D ∧ {s : ℂ | 1 ≤ s.re} ⊆ D ∧
      DifferentiableOn ℂ cand D ∧ Set.EqOn cand F {s : ℂ | 1 < s.re} := by
  classical
  set P : Set ℂ := {s : ℂ | 1 < s.re} with hP
  set cand : ℂ → ℂ := fun s => if 1 < s.re then F s else G s with hcand
  refine ⟨cand, U ∪ P, hU.union isOpen_one_lt_re, ?_, ?_, ?_⟩
  · -- the closed half-plane is covered
    intro s hs
    have hs' : (1:ℝ) ≤ s.re := hs
    rcases lt_or_eq_of_le hs' with hgt | heq
    · exact Or.inr hgt
    · exact Or.inl (hUline heq.symm)
  · -- holomorphy: local, and each point sees one piece outright
    have hcandU : Set.EqOn cand G U := by
      intro t ht
      rw [hcand]
      by_cases h : 1 < t.re
      · simp only [if_pos h]
        exact (hGF ⟨ht, h⟩).symm
      · simp only [if_neg h]
    have hcandP : Set.EqOn cand F P := by
      intro t ht
      rw [hcand]
      simp only [if_pos (show 1 < t.re from ht)]
    intro s hs
    refine DifferentiableAt.differentiableWithinAt ?_
    rcases hs with hsU | hsP
    · have hev : cand =ᶠ[𝓝 s] G :=
        Filter.eventuallyEq_of_mem (hU.mem_nhds hsU) hcandU
      exact (hev.differentiableAt_iff).mpr
        ((hG s hsU).differentiableAt (hU.mem_nhds hsU))
    · have hev : cand =ᶠ[𝓝 s] F :=
        Filter.eventuallyEq_of_mem (isOpen_one_lt_re.mem_nhds hsP) hcandP
      exact (hev.differentiableAt_iff).mpr
        ((hF s hsP).differentiableAt (isOpen_one_lt_re.mem_nhds hsP))
  · intro t ht
    rw [hcand]
    simp only [if_pos (show 1 < t.re from ht)]

end CriticalLinePhasor.ThreeDConverse

#print axioms CriticalLinePhasor.ThreeDConverse.exists_halfplane_extension_of_line_neighborhood
