import Mathlib

/-!
# Reflections divide: the functional equation is never the obstruction

The meet-in-the-middle junction lemma.  The campaign holds the chain's two
ends: from below, the converse ring and the completeness-to-entirety upgrade;
from above, the seed's modularity, the compiled low-rank crossings, and the
tower's quotient identities.  This file proves the junction fact
that joins the ends: in the analytic register, reflections divide.

* `reflection_of_factor` — if a product `B·C` satisfies the `s ↦ 1−s`
  reflection on a reflection-stable preconnected open set, and the factor `C`
  satisfies its own reflection and is not identically zero, then `B` satisfies
  the induced reflection on the whole set.  No division is performed: the
  proof multiplies the product identity by the factor identity and kills the
  discrepancy by the identity theorem, so no pole or zero of `C` pollutes the
  conclusion;
* `quotient_reflection` — the packaging for the tower's quotient rungs: a
  completed pair with a functional equation, factored through a completed
  denominator with a functional equation, transfers the functional equation to
  the quotient wherever the quotient is analytic.

Register: the reduction this compiles.  Every tower identity
(`TensorTowerBanks`) writes a higher rung as pair-over-denominator; this lemma
says the **functional-equation half of every such rung is free** — for the
known pairs (`r ≤ 9`, Kim–Shahidi) and for any future pair, once the pair has
its reflection the rung inherits it.  The completeness route
(`entireness-gap` resolution: no trivial channel ⟹ zero common mode)
addresses entirety.  What remains of one-sided niceness at any quotient rung
is therefore exactly **zero-containment**: the zeros of the denominator's
completion must lie among the zeros of the pair's completion,
`Z(Λ_C) ⊆ Z(Λ_P)`.  The missing object of the whole program, after this
lemma, is a statement about zero sets — the territory of the house's oldest
compiled instruments (the zero-detection pencil, the `S(t)` registration
theory).  Scope: the lemma consumes analyticity of `B` on the region — it
transfers the reflection to an existing extension and does not manufacture
the extension.  No `axiom`, no `sorry`.
-/

open Filter Topology

namespace CriticalLinePhasor.ReflectionDivision

/-- **Reflections divide.**  On a reflection-stable preconnected open set: if
`B·C` reflects with sign `ε`, `C` reflects with sign `εC` and is not
identically zero, then `εC·B s = ε·B (1−s)` throughout. -/
theorem reflection_of_factor {U : Set ℂ} (hU : IsOpen U) (hUc : IsPreconnected U)
    {B C : ℂ → ℂ} (hB : AnalyticOnNhd ℂ B U) (hC : AnalyticOnNhd ℂ C U)
    {ε εC : ℂ}
    (hrefl : ∀ s ∈ U, (1 : ℂ) - s ∈ U)
    (hprod : ∀ s ∈ U, B s * C s = ε * (B (1 - s) * C (1 - s)))
    (hCrefl : ∀ s ∈ U, C s = εC * C (1 - s))
    {z₀ : ℂ} (hz₀ : z₀ ∈ U) (hCz₀ : C z₀ ≠ 0) :
    ∀ s ∈ U, εC * B s = ε * B (1 - s) := by
  set g : ℂ → ℂ := fun s => εC * B s - ε * B (1 - s) with hg
  have hBrefl : AnalyticOnNhd ℂ (fun s => B (1 - s)) U := by
    intro z hz
    have h1 : AnalyticAt ℂ (fun s : ℂ => (1 : ℂ) - s) z :=
      analyticAt_const.sub analyticAt_id
    exact (hB _ (hrefl z hz)).comp h1
  have hgan : AnalyticOnNhd ℂ g U := by
    intro z hz
    exact (analyticAt_const.mul (hB z hz)).sub
      (analyticAt_const.mul (hBrefl z hz))
  have hgC : ∀ s ∈ U, g s * C s = 0 := by
    intro s hs
    have h1 := hprod s hs
    have h2 := hCrefl s hs
    have h3 : εC * (B s * C s) = ε * (B (1 - s) * (εC * C (1 - s))) := by
      rw [h1]
      ring
    rw [← h2] at h3
    simp only [hg]
    linear_combination h3
  have hev : ∀ᶠ w in 𝓝 z₀, C w ≠ 0 :=
    ((hC z₀ hz₀).continuousAt).eventually_ne hCz₀
  have hgz : g =ᶠ[𝓝 z₀] 0 := by
    filter_upwards [hev, hU.mem_nhds hz₀] with w hw hwU
    have hzero := hgC w hwU
    exact (mul_eq_zero.mp hzero).resolve_right hw
  have hall := hgan.eqOn_zero_of_preconnected_of_eventuallyEq_zero hUc hz₀ hgz
  intro s hs
  have hgs := hall hs
  simp only [hg, Pi.zero_apply] at hgs
  linear_combination hgs

/-- **Quotient rungs inherit the functional equation.**  If a completed pair
`P` reflects with sign `εP`, factors as `P = B·C` on the region, and the
completed denominator `C` reflects with sign `εC` and is not identically
zero, then the quotient `B` reflects: `εC·B s = εP·B (1−s)`. -/
theorem quotient_reflection {U : Set ℂ} (hU : IsOpen U) (hUc : IsPreconnected U)
    {P B C : ℂ → ℂ} (hB : AnalyticOnNhd ℂ B U) (hC : AnalyticOnNhd ℂ C U)
    {εP εC : ℂ}
    (hrefl : ∀ s ∈ U, (1 : ℂ) - s ∈ U)
    (hPrefl : ∀ s ∈ U, P s = εP * P (1 - s))
    (hfact : ∀ s ∈ U, P s = B s * C s)
    (hCrefl : ∀ s ∈ U, C s = εC * C (1 - s))
    {z₀ : ℂ} (hz₀ : z₀ ∈ U) (hCz₀ : C z₀ ≠ 0) :
    ∀ s ∈ U, εC * B s = εP * B (1 - s) := by
  refine reflection_of_factor hU hUc hB hC hrefl ?_ hCrefl hz₀ hCz₀
  intro s hs
  have h1 := hPrefl s hs
  rw [hfact s hs, hfact (1 - s) (hrefl s hs)] at h1
  exact h1

end CriticalLinePhasor.ReflectionDivision

#print axioms CriticalLinePhasor.ReflectionDivision.reflection_of_factor
#print axioms CriticalLinePhasor.ReflectionDivision.quotient_reflection
