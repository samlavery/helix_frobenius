import RequestProject.ReflectionDivision

/-!
# The zero-containment target: the program's frontier as one typed object

After `ReflectionDivision` (the functional equation of every quotient rung is
free) and the completeness route (entirety from no-trivial-channel, the
adapter resolution), the remaining content of one-sided niceness at a quotient
rung is exactly **zero-containment with growth**: the quotient of the pair's
completed function by the denominator's extends entirely and is bounded on
vertical strips.  This file compiles that frontier as a single structure and
proves the assembly:

* `ContainmentData` — the typed target: an entire quotient `B` realizing
  `P = B·C`, with vertical-strip bounds.  Its `entire` field **is** the
  zero-containment statement `Z(C) ⊆ Z(P)` (with multiplicity): the poles the
  ratio would have at the denominator's zeros are absorbed;
* `containment_analytic_package` — **the assembly**: pair package (entire,
  functional equation, strip bounds — for the known pairs this is
  Jacquet--Piatetski-Shapiro--Shalika, cited) + denominator package (for
  `Sym³`, Kim--Shahidi, cited) + `ContainmentData` produce the quotient's full
  analytic package: entire, functional equation with the quotient sign, strip
  bounds.  The functional equation comes from `quotient_reflection` at
  `U = ℂ` — no division, no grade loss.

Register.  Rung-five instantiation: `P = Λ(f × Sym⁴f)`, `C = Λ(Sym³f)`,
`B = Λ(Sym⁵f)`; `ContainmentData` there is exactly
`Z(Λ(Sym³f)) ⊆ Z(Λ(f×Sym⁴f))` plus growth, and this theorem converts it into
the `Sym⁵` analytic package that feeds the converse machinery.  Structural
note from the witness sweep: every decomposition of a known automorphic pair
containing `Sym⁵` carries the *same* cofactor `Sym³` (Clebsch--Gordan fusion
steps by two), so no two-witness common-zero argument is available — the
containment must be faced at this single interface.  The chart identity of
the quotient (its Dirichlet readout) is supplied separately by the compiled
bank factorizations (`tensorQuintic_bank`) on the common convergence region
and is not part of this file's claim.  No `axiom`, no `sorry`.
-/

open Filter Topology

namespace CriticalLinePhasor.ZeroContainment

open CriticalLinePhasor.ReflectionDivision

/-- **The typed frontier**: an entire, strip-bounded realization of the
quotient.  The `entire` field is zero-containment with multiplicity; `bound`
is the growth half. -/
structure ContainmentData (P C : ℂ → ℂ) where
  quotient : ℂ → ℂ
  factor : ∀ s : ℂ, P s = quotient s * C s
  entire : Differentiable ℂ quotient
  bound : ∀ u v : ℝ, ∃ M : ℝ, ∀ s : ℂ, u ≤ s.re → s.re ≤ v → ‖quotient s‖ ≤ M

/-- **The assembly**: pair package + denominator package + containment data
give the quotient's full analytic package — entire, reflected, bounded on
every vertical strip. -/
theorem containment_analytic_package
    {P C : ℂ → ℂ} {εP εC : ℂ}
    (hPrefl : ∀ s : ℂ, P s = εP * P (1 - s))
    (hC : Differentiable ℂ C)
    (hCrefl : ∀ s : ℂ, C s = εC * C (1 - s))
    {z₀ : ℂ} (hCz₀ : C z₀ ≠ 0)
    (D : ContainmentData P C) :
    Differentiable ℂ D.quotient ∧
    (∀ s : ℂ, εC * D.quotient s = εP * D.quotient (1 - s)) ∧
    (∀ u v : ℝ, ∃ M : ℝ, ∀ s : ℂ, u ≤ s.re → s.re ≤ v → ‖D.quotient s‖ ≤ M) := by
  refine ⟨D.entire, ?_, D.bound⟩
  have hBan : AnalyticOnNhd ℂ D.quotient Set.univ := by
    intro z _
    exact D.entire.analyticAt z
  have hCan : AnalyticOnNhd ℂ C Set.univ := by
    intro z _
    exact hC.analyticAt z
  have h := quotient_reflection (U := Set.univ) isOpen_univ isPreconnected_univ
    hBan hCan (fun s _ => Set.mem_univ _)
    (fun s _ => hPrefl s) (fun s _ => D.factor s) (fun s _ => hCrefl s)
    (Set.mem_univ z₀) hCz₀
  intro s
  exact h s (Set.mem_univ s)

/-- Containment is monotone in the factorization: the quotient's zeros join the
denominator's inside the pair — the pair vanishes wherever either factor
does. -/
theorem pair_vanishes_of_factor {P C : ℂ → ℂ} (D : ContainmentData P C)
    {z : ℂ} (hz : C z = 0 ∨ D.quotient z = 0) : P z = 0 := by
  rcases hz with h | h <;> rw [D.factor z, h] <;> ring

end CriticalLinePhasor.ZeroContainment

#print axioms CriticalLinePhasor.ZeroContainment.containment_analytic_package
#print axioms CriticalLinePhasor.ZeroContainment.pair_vanishes_of_factor
