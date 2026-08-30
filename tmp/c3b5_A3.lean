import Mathlib

/-!
# C3 batch 5, block A3 — the Riccati ceiling `−z′/z ≤ 1`, by ONE monotonicity

This is the analytic input consumed by `C3B5.A2.radial_pos`.  Block A2 assumed
`ρ ≤ 1` where `ρ = −z′/z` and `z(A) = A^{1/2}K_{ix}(A)`.  Here that ceiling is proved,
and the two changes of variable that produce it are verified as exact algebra.

## The argument, and why it is short

The obvious route is a blow-up contradiction: `ρ′ = ρ² − q ≥ ρ² − 1 > 0` when `ρ > 1`,
so `ρ` escapes to `+∞` in finite `A`, i.e. `z` acquires a zero, contradicting
disconjugacy above the turning point.  That needs disconjugacy, a Riccati
comparison, and a finite-time escape estimate.

It is not needed.  Put `W := z + z′`.  Then

  `W′ − W = (z′ + z″) − (z + z′) = z″ − z = (q − 1)·z ≤ 0`

using only `z″ = q·z`, `q ≤ 1` and `z > 0`.  So `e^{−A}W` is nonincreasing; it tends to
`0` at `+∞` because `z` and `z′` do; a nonincreasing function with limit `0` at `+∞` is
nonnegative.  Hence `W ≥ 0`, i.e. `−z′/z ≤ 1`.

No disconjugacy, no turning point, no contradiction — and the hypothesis is weaker
(`q ≤ 1` only, which holds for **every** `A > 0`, not just `A > A*`).  The turning point
is still where the *other* Riccati bound `ρ ≥ √q` and the no-zero statement live, but
neither is used by `radial_pos`.

## Contents

1. `nonneg_of_deriv_le_self` — the monotonicity core, stated for a general `W`.
2. `logDeriv_le_one` — the ceiling `−z′/z ≤ 1`.
3. `liouville_normal_form` — the modified-Bessel equation becomes `z″ = q·z` with
   `q = 1 − (x²+¼)/A²`, verified as exact algebra in `r = √A`.
4. `liouville_logDeriv` — `K′/K = −ρ − 1/(2A)`, i.e. exactly the `hlog` hypothesis of
   block A2, produced rather than assumed.
5. `riccati_hasDerivAt`, `riccati_comparison` — the Riccati identity `ρ′ = ρ² − q` and
   the blow-up comparison, recorded because they are the route this file *replaces*.

SCOPE: no `Ξ`, no zeros, no RH.  ODE-free real analysis plus algebra.
-/

open Real Set Filter Topology

noncomputable section

namespace C3B5.A3

/-! ### 1. The monotonicity core -/

/-- **If `W′ ≤ W` on `[a,∞)` and `W → 0` at `+∞`, then `W ≥ 0` on `[a,∞)`.**
The whole content of the Riccati ceiling. -/
theorem nonneg_of_deriv_le_self {W : ℝ → ℝ} {a : ℝ}
    (hdiff : ∀ t ∈ Ici a, DifferentiableAt ℝ W t)
    (hle : ∀ t ∈ Ici a, deriv W t ≤ W t)
    (hlim : Tendsto W atTop (nhds 0)) :
    ∀ t ∈ Ici a, 0 ≤ W t := by
  set g : ℝ → ℝ := fun t => Real.exp (-t) * W t with hg
  have hgd : ∀ t ∈ Ici a, HasDerivAt g (Real.exp (-t) * (deriv W t - W t)) t := by
    intro t ht
    have h1 : HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-t)) t := by
      have := (hasDerivAt_neg t).exp
      simpa using this
    have h2 : HasDerivAt W (deriv W t) t := (hdiff t ht).hasDerivAt
    have := h1.mul h2
    refine this.congr_deriv ?_
    ring
  -- `g` is antitone on `[a,∞)`
  have hcont : ContinuousOn g (Ici a) := fun t ht =>
    ((hgd t ht).continuousAt).continuousWithinAt
  have hanti : AntitoneOn g (Ici a) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici a) hcont ?_ ?_
    · intro t ht
      rw [interior_Ici] at ht
      have hmem : t ∈ Ici a := Set.mem_Ici.mpr (le_of_lt (Set.mem_Ioi.mp ht))
      exact ((hgd t hmem).differentiableAt).differentiableWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      have hmem : t ∈ Ici a := Set.mem_Ici.mpr (le_of_lt (Set.mem_Ioi.mp ht))
      rw [(hgd t hmem).deriv]
      have hsub : deriv W t - W t ≤ 0 := by linarith [hle t hmem]
      exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hsub
  -- `g → 0` at `+∞`
  have hglim : Tendsto g atTop (nhds 0) := by
    have hexp : Tendsto (fun t : ℝ => Real.exp (-t)) atTop (nhds 0) :=
      Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
    simpa [hg] using hexp.mul hlim
  intro t ht
  have hev : ∀ᶠ s in atTop, g s ≤ g t := by
    filter_upwards [eventually_ge_atTop t] with s hs
    exact hanti ht (le_trans ht hs) hs
  have h0 : (0 : ℝ) ≤ g t := le_of_tendsto hglim hev
  have hexp : 0 < Real.exp (-t) := Real.exp_pos _
  have : 0 ≤ Real.exp (-t) * W t := h0
  exact nonneg_of_mul_nonneg_right this hexp

/-- **THE RICCATI CEILING.**  With `z > 0`, `z″ = q·z`, `q ≤ 1`, and `z, z′ → 0` at
`+∞`, the logarithmic decay rate of `z` never exceeds `1`. -/
theorem logDeriv_le_one {z zd zdd q : ℝ → ℝ} {a : ℝ}
    (hz : ∀ t ∈ Ici a, 0 < z t)
    (hzd : ∀ t ∈ Ici a, HasDerivAt z (zd t) t)
    (hzdd : ∀ t ∈ Ici a, HasDerivAt zd (zdd t) t)
    (hode : ∀ t ∈ Ici a, zdd t = q t * z t)
    (hq : ∀ t ∈ Ici a, q t ≤ 1)
    (hlim : Tendsto (fun t => z t + zd t) atTop (nhds 0)) :
    ∀ t ∈ Ici a, -zd t / z t ≤ 1 := by
  set W : ℝ → ℝ := fun t => z t + zd t with hW
  have hWd : ∀ t ∈ Ici a, HasDerivAt W (zd t + zdd t) t := fun t ht =>
    (hzd t ht).add (hzdd t ht)
  have hdiff : ∀ t ∈ Ici a, DifferentiableAt ℝ W t := fun t ht =>
    (hWd t ht).differentiableAt
  have hle : ∀ t ∈ Ici a, deriv W t ≤ W t := by
    intro t ht
    rw [(hWd t ht).deriv, hW]
    have h1 : zdd t = q t * z t := hode t ht
    have h2 : q t * z t ≤ z t := by
      have := hz t ht
      nlinarith [hq t ht]
    simp only []
    linarith
  have hWnn := nonneg_of_deriv_le_self hdiff hle hlim
  intro t ht
  have h1 : 0 ≤ z t + zd t := hWnn t ht
  have h2 : 0 < z t := hz t ht
  rw [div_le_one h2]
  linarith

/-! ### 2. The two changes of variable, as exact algebra -/

/-- **The Liouville normal form of the modified Bessel equation, verified.**
Writing `A = r²` (`r = √A > 0`), the substitution `z = r·K` turns

  `A²K″ + A·K′ − (A² − x²)K = 0`   into   `z″ = (1 − (x²+¼)/A²)·z`,

where the left side below is literally `z″ = −¼r^{−3}K + r^{−1}K′ + r·K″`. -/
theorem liouville_normal_form {r K K' K'' x : ℝ} (hr : 0 < r)
    (hbessel : r ^ 4 * K'' + r ^ 2 * K' - (r ^ 4 - x ^ 2) * K = 0) :
    -(1 / (4 * r ^ 3)) * K + (1 / r) * K' + r * K''
      = (1 - (x ^ 2 + 1 / 4) / r ^ 4) * (r * K) := by
  have hr0 : r ≠ 0 := hr.ne'
  have key : -(1 / (4 * r ^ 3)) * K + (1 / r) * K' + r * K''
      - (1 - (x ^ 2 + 1 / 4) / r ^ 4) * (r * K)
      = (1 / r ^ 3) * (r ^ 4 * K'' + r ^ 2 * K' - (r ^ 4 - x ^ 2) * K) := by
    field_simp
    ring
  rw [hbessel, mul_zero] at key
  linarith

/-- **The Liouville gauge shifts the logarithmic derivative by `1/(2A)`.**
If `HasDerivAt K K' A` and `A > 0`, then `z = √A·K` has
`z′/z = K′/K + 1/(2A)`; equivalently `K′ = −(ρ + 1/(2A))·K` with `ρ = −z′/z`.
This produces the `hlog` hypothesis of block A2 instead of assuming it. -/
theorem liouville_logDeriv {K : ℝ → ℝ} {K' A : ℝ} (hA : 0 < A)
    (hK : HasDerivAt K K' A) :
    HasDerivAt (fun t => Real.sqrt t * K t)
      (Real.sqrt A * (K' + K A / (2 * A))) A := by
  have hs : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt A)) A :=
    Real.hasDerivAt_sqrt hA.ne'
  have h := hs.mul hK
  refine h.congr_deriv ?_
  have hsq : Real.sqrt A ^ 2 = A := Real.sq_sqrt hA.le
  have hsp : 0 < Real.sqrt A := Real.sqrt_pos.mpr hA
  field_simp
  linear_combination (-(K A)) * hsq

/-- The algebraic consequence: `ρ := −z′/z` and `K′/K` differ by exactly `1/(2A)`, so
`K′ = −(ρ + 1/(2A))·K`, which is the literal `hlog` of `C3B5.A2.radial_pos`. -/
theorem logDeriv_transfer {A K K' zd z : ℝ} (hA : 0 < A) (hK : K ≠ 0) (hz : z ≠ 0)
    (hzval : z = Real.sqrt A * K)
    (hzd : zd = Real.sqrt A * (K' + K / (2 * A))) :
    K' = -((-zd / z) + 1 / (2 * A)) * K := by
  have hsp : 0 < Real.sqrt A := Real.sqrt_pos.mpr hA
  subst hzval hzd
  field_simp
  ring

/-! ### 3. The route this file replaces, recorded -/

/-- **The Riccati identity** `ρ′ = ρ² − q` for `ρ = −z′/z`, from the quotient rule. -/
theorem riccati_hasDerivAt {Z Zd : ℝ → ℝ} {q t : ℝ}
    (hZ : HasDerivAt Z (Zd t) t) (hZd : HasDerivAt Zd (q * Z t) t) (hne : Z t ≠ 0) :
    HasDerivAt (fun s => -(Zd s / Z s)) ((-(Zd t / Z t)) ^ 2 - q) t := by
  have h := (hZd.div hZ hne).neg
  refine h.congr_deriv ?_
  field_simp
  ring

/-- **The blow-up comparison.**  Above the ceiling the Riccati right-hand side dominates
the model `σ′ ≤ −1` for `σ = 1/(ρ−1)`: `(ρ−1)² ≤ ρ² − q` whenever `ρ > 1` and `q ≤ 1`.
Kept for the record — `logDeriv_le_one` does not need it. -/
theorem riccati_comparison {ρ q : ℝ} (hρ : 1 < ρ) (hq : q ≤ 1) :
    (ρ - 1) ^ 2 ≤ ρ ^ 2 - q := by nlinarith

/-- The turning-point sign of the Liouville potential: `q(A) = 1 − (x²+¼)/A² > 0`
exactly above `A* = √(x²+¼)`.  (Used for the *other* Riccati bound, not for the
ceiling.) -/
theorem liouville_potential_pos {A x : ℝ} (hA : 0 < A) (hstar : Real.sqrt (x ^ 2 + 1 / 4) < A) :
    0 < 1 - (x ^ 2 + 1 / 4) / A ^ 2 := by
  have hnn : (0 : ℝ) ≤ x ^ 2 + 1 / 4 := by positivity
  have hsq : Real.sqrt (x ^ 2 + 1 / 4) ^ 2 = x ^ 2 + 1 / 4 := Real.sq_sqrt hnn
  have hs0 : 0 ≤ Real.sqrt (x ^ 2 + 1 / 4) := Real.sqrt_nonneg _
  have hlt : x ^ 2 + 1 / 4 < A ^ 2 := by nlinarith
  have hA2 : (0 : ℝ) < A ^ 2 := by positivity
  rw [sub_pos, div_lt_one hA2]
  exact hlt

end C3B5.A3

section AxiomAudit
#print axioms C3B5.A3.nonneg_of_deriv_le_self
#print axioms C3B5.A3.logDeriv_le_one
#print axioms C3B5.A3.liouville_normal_form
#print axioms C3B5.A3.liouville_logDeriv
#print axioms C3B5.A3.logDeriv_transfer
#print axioms C3B5.A3.riccati_hasDerivAt
#print axioms C3B5.A3.riccati_comparison
#print axioms C3B5.A3.liouville_potential_pos
end AxiomAudit
