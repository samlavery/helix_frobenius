import RequestProject.GeometricSourceRecognition

/-!
# Abelian clock projectors: the `[n]`-graph dictionary, degree-scoped

The clock ↔ multiplication-graph dictionary at its SAFE scope (review
correction, 2026-07-28):

    carrier clock decomposition ⟷ the algebraic [n]-correspondence
                                   decomposition of h(A)

— projectors onto cohomological DEGREES and endomorphism-cut motivic
factors, never onto arbitrary individual classes within one degree.

Model: degree channels `0..2g`; the clock of `[n]` scales channel `i` by
`n^i` — the cohomological action of the multiplication-by-`n` graph on an
abelian variety of dimension `g`.  The graph algebra is the ℚ-span of the
clocks of `[1], …, [2g+1]`.  External input (cited, Deninger–Murre
context): the `[n]`-graphs are algebraic correspondences; hence every
element of the graph algebra is algebraic BY CONSTRUCTION — provenance,
not conjecture.  In-kernel content:

* `vandermonde_delta` — the Vandermonde/Lagrange inversion over ℚ:
  rational coefficients hitting any degree-delta pattern;
* `degreeProjector_in_graphAlgebra` — every degree projector IS an
  explicit element of the graph algebra;
* `degree_component_manufactured` — every degree component of every seed
  state is the image of that seed under an explicit graph-algebra
  correspondence: the manufacture theorem at degree scope, feeding
  `ProjectorRecognition` for degree-graded factors.

Rational coefficients throughout — the ℚ-linearity of the Chow groups is
respected, no real limits taken.  Scope: does not assume or prove RH/GRH
or the Hodge conjecture; degree scope only.
-/

namespace CriticalLinePhasor.HodgeLedgerFiltration

namespace AbelianClock

variable {order g : ℕ}

/-- The clock of `[n]`: channel `i` (cohomological degree `i`) scales by
`n^i` — the model avatar of the multiplication-by-`n` graph. -/
noncomputable def mulClock (n : ℕ) (z : GeneralExtensionData order (2*g+1)) :
    GeneralExtensionData order (2*g+1) :=
  fun l i => ((n : ℂ)) ^ (i : ℕ) * z l i

/-- The graph algebra: formal ℚ-combinations of the clocks of
`[1], …, [2g+1]` — every element algebraic by construction (combinations
of graphs). -/
def GraphCorr (g : ℕ) := Fin (2*g+1) → ℚ

/-- Action of a graph-algebra element: `Σ_k c k · [k+1]`-clock. -/
noncomputable def graphAct (c : GraphCorr g)
    (z : GeneralExtensionData order (2*g+1)) :
    GeneralExtensionData order (2*g+1) :=
  fun l i => (∑ k : Fin (2*g+1), (c k : ℂ) * (((k : ℕ) + 1 : ℕ) : ℂ) ^ (i : ℕ)) * z l i

/-- The degree projector (semantic target). -/
noncomputable def degreeProj (i₀ : Fin (2*g+1))
    (z : GeneralExtensionData order (2*g+1)) :
    GeneralExtensionData order (2*g+1) :=
  fun l i => if i = i₀ then z l i else 0

/-- **Vandermonde inversion over ℚ**: rational coefficients realizing any
degree delta — the in-kernel half of Deninger–Murre. -/
theorem vandermonde_delta (g : ℕ) (i₀ : Fin (2*g+1)) :
    ∃ c : Fin (2*g+1) → ℚ, ∀ i : Fin (2*g+1),
      (∑ k : Fin (2*g+1), c k * (((k : ℕ) + 1 : ℚ)) ^ (i : ℕ))
        = if i = i₀ then 1 else 0 := by
  set v : Fin (2*g+1) → ℚ := fun k => ((k : ℕ) : ℚ) + 1 with hv
  have hvinj : Function.Injective v := by
    intro a b hab
    simp only [hv] at hab
    have : ((a : ℕ) : ℚ) = ((b : ℕ) : ℚ) := by linarith
    exact Fin.ext (Nat.cast_injective this)
  set V := Matrix.vandermonde v with hV
  have hdet : V.det ≠ 0 := by
    rw [hV, Matrix.det_vandermonde]
    refine Finset.prod_ne_zero_iff.mpr fun i _ => ?_
    refine Finset.prod_ne_zero_iff.mpr fun j hj => ?_
    have hij : i ≠ j := by
      intro h
      subst h
      simp [Finset.mem_Ioi] at hj
    exact sub_ne_zero_of_ne fun h => hij (hvinj h.symm)
  have hdetT : (V.transpose).det ≠ 0 := by
    rwa [Matrix.det_transpose]
  have hunit : IsUnit (V.transpose).det := isUnit_iff_ne_zero.mpr hdetT
  set c : Fin (2*g+1) → ℚ := (V.transpose)⁻¹.mulVec (Pi.single i₀ 1)
    with hcdef
  refine ⟨c, fun i => ?_⟩
  have hmv : (V.transpose).mulVec c = Pi.single i₀ 1 := by
    rw [hcdef, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hunit,
      Matrix.one_mulVec]
  have hi := congrFun hmv i
  rw [Pi.single_apply] at hi
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply,
    hV, Matrix.vandermonde_apply] at hi
  rw [← hi]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [hv]
  push_cast
  ring

/-- **Every degree projector lies in the graph algebra**: an explicit
ℚ-combination of multiplication clocks acts as the exact projector onto
degree `i₀` — algebraic by construction in the avatar. -/
theorem degreeProjector_in_graphAlgebra (i₀ : Fin (2*g+1)) :
    ∃ c : GraphCorr g, ∀ (z : GeneralExtensionData order (2*g+1)) l i,
      graphAct c z l i = degreeProj i₀ z l i := by
  obtain ⟨c, hc⟩ := vandermonde_delta g i₀
  refine ⟨c, fun z l i => ?_⟩
  have hcast : (∑ k : Fin (2*g+1), (c k : ℂ) * (((k : ℕ) + 1 : ℕ) : ℂ) ^ (i : ℕ))
      = ((∑ k : Fin (2*g+1), c k * (((k : ℕ) + 1 : ℚ)) ^ (i : ℕ) : ℚ) : ℂ) := by
    push_cast
    rfl
  simp only [graphAct, degreeProj, hcast, hc i]
  by_cases h : i = i₀
  · simp [h]
  · simp [h]

/-- **The manufacture theorem, degree scope**: every degree component of
every seed is the image of the seed under an explicit graph-algebra
correspondence — `π_{i₀}(η)` with `π_{i₀}` algebraic by provenance.  This
feeds `ProjectorRecognition` for degree-graded motivic factors; it does
NOT manufacture projectors onto individual classes within a degree. -/
theorem degree_component_manufactured (i₀ : Fin (2*g+1))
    (η : GeneralExtensionData order (2*g+1)) :
    ∃ c : GraphCorr g, graphAct c η = degreeProj i₀ η := by
  obtain ⟨c, hc⟩ := degreeProjector_in_graphAlgebra i₀
  exact ⟨c, funext fun l => funext fun i => hc η l i⟩

end AbelianClock

end CriticalLinePhasor.HodgeLedgerFiltration

#print axioms CriticalLinePhasor.HodgeLedgerFiltration.AbelianClock.vandermonde_delta
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.AbelianClock.degreeProjector_in_graphAlgebra
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.AbelianClock.degree_component_manufactured
