import RequestProject.NoPositiveDecayingSolution
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The repair, certified: the Whittaker equation flips the sign

`no_positive_decaying_solution` kills `g'' − 4πg' = c·g/y²` for every `c ≥ 0`, and the structure's
`radial_equation` delivers `c = r² ≥ 0`.  This file computes `c` for the **corrected** equation and
finds it strictly negative — so the emptiness argument does not merely fail to apply, it is
outside its range by a definite margin.

Setting `R := e^{2πy}K`, the Whittaker equation `y²K'' + y·K' = ((2πy)² − r²)K` becomes

  **`y²R'' + (1 − 4πy)·y·R' + (r² − 2πy)·R = 0`,**

and the normalization quantity `S := 2√y·R` — the thing `radial_normalization` requires to tend to
`1` — then satisfies

  **`y²S'' − 4πy²S' = −(1/4 + r²)·S`,   i.e.   `S'' − 4πS' = c·S/y²` with `c = −(1/4 + r²) < 0`.**

Against the structure's own equation the same quantity gives `c = +r² ≥ 0`
(`realReduced_equation`, `maass_empty_at_zero`).  So the two candidate radial equations sit on
opposite sides of the one inequality that decides whether `2√y·e^{2πy}·K(y) → 1` is possible, and
the missing first-order term `y·K'` is exactly what moves it across.

The mechanism is visible in the computation: the `−4πy²R'` and `−2πyR` terms cancel identically
against each other at weight `y^{1/2}`, which is what lets `S` sit at a constant.  With the
first-order term absent there is no `−2πyR` to do the cancelling.
-/

open Filter
open scoped Real Topology

namespace CriticalLinePhasor.ThreeDConverse

/-- **The `√y` weight, and the sign flip.**  If `R` satisfies the reduced Whittaker equation
`y²R'' + (1 − 4πy)yR' + (a − 2πy)R = 0`, then `S = 2√y·R` satisfies `y²S'' − 4πy²S' = −(1/4+a)S`.

With `a = r² ≥ 0` the coefficient `−(1/4 + a)` is **strictly negative**, whereas the structure's
`radial_equation` yields `+r² ≥ 0` — the range in which `no_positive_decaying_solution` forces a
contradiction. -/
theorem sqrt_weight_sign_flip
    {a : ℝ} {R : ℝ → ℝ}
    (hR1 : ∀ y : ℝ, 0 < y → DifferentiableAt ℝ R y)
    (hR2 : ∀ y : ℝ, 0 < y → DifferentiableAt ℝ (deriv R) y)
    (hRode : ∀ y : ℝ, 0 < y →
      y ^ 2 * deriv (deriv R) y + (1 - 4 * Real.pi * y) * y * deriv R y
        + (a - 2 * Real.pi * y) * R y = 0)
    {y : ℝ} (hy : 0 < y) :
    y ^ 2 * deriv (deriv (fun t : ℝ => 2 * Real.sqrt t * R t)) y
        - 4 * Real.pi * y ^ 2 * deriv (fun t : ℝ => 2 * Real.sqrt t * R t) y
      = -(1 / 4 + a) * (2 * Real.sqrt y * R y) := by
  -- the first derivative of `S = 2√t·R`
  have hS1 : ∀ t : ℝ, 0 < t → HasDerivAt (fun u : ℝ => 2 * Real.sqrt u * R u)
      (R t / Real.sqrt t + 2 * Real.sqrt t * deriv R t) t := by
    intro t ht
    have hst : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr ht).ne'
    refine (((Real.hasDerivAt_sqrt ht.ne').const_mul 2).mul (hR1 t ht).hasDerivAt).congr_deriv ?_
    field_simp
  have hd1 : deriv (fun t : ℝ => 2 * Real.sqrt t * R t) =ᶠ[𝓝 y]
      fun t : ℝ => R t / Real.sqrt t + 2 * Real.sqrt t * deriv R t := by
    filter_upwards [Ioi_mem_nhds hy] with t ht
    exact (hS1 t ht).deriv
  -- the second derivative
  have hs0 : Real.sqrt y ≠ 0 := (Real.sqrt_pos.mpr hy).ne'
  have hS2 : HasDerivAt (fun u : ℝ => R u / Real.sqrt u + 2 * Real.sqrt u * deriv R u)
      ((deriv R y * Real.sqrt y - R y * (1 / (2 * Real.sqrt y))) / Real.sqrt y ^ 2
        + ((2 * (1 / (2 * Real.sqrt y))) * deriv R y
            + 2 * Real.sqrt y * deriv (deriv R) y)) y :=
    ((hR1 y hy).hasDerivAt.div (Real.hasDerivAt_sqrt hy.ne') hs0).add
      (((Real.hasDerivAt_sqrt hy.ne').const_mul 2).mul (hR2 y hy).hasDerivAt)
  rw [hd1.deriv_eq, hS2.deriv, (hS1 y hy).deriv]
  -- write `y = s²` so that `√y` is a polynomial variable
  obtain ⟨s, hspos, rfl⟩ : ∃ s : ℝ, 0 < s ∧ y = s ^ 2 :=
    ⟨Real.sqrt y, Real.sqrt_pos.mpr hy, (Real.sq_sqrt hy.le).symm⟩
  rw [Real.sqrt_sq hspos.le] at *
  have hode := hRode (s ^ 2) hy
  have hR'' : deriv (deriv R) (s ^ 2)
      = (-(1 - 4 * Real.pi * s ^ 2) * s ^ 2 * deriv R (s ^ 2)
          - (a - 2 * Real.pi * s ^ 2) * R (s ^ 2)) / s ^ 4 := by
    field_simp
    linear_combination hode
  rw [hR'']
  field_simp
  ring

end CriticalLinePhasor.ThreeDConverse

#print axioms CriticalLinePhasor.ThreeDConverse.sqrt_weight_sign_flip
