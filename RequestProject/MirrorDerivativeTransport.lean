import Mathlib

/-!
# Mirror transport of the derivative at an event, for the GRH fibers (ledger 661)

Mathlib's functional equation for a primitive Dirichlet character `χ` mod `N`:
`Λ(1 − s, χ) = N^{s−½} · ε(χ) · Λ(s, χ⁻¹)` (`IsPrimitive.completedLFunction_one_sub`).
Differentiating it in `s` gives, at a zero `s₀` of `Λ(·, χ⁻¹)`:

* `Λ(1 − s₀, χ) = 0` (the mirror event), and
* `Λ′(1 − s₀, χ) = − N^{s₀−½} · ε(χ) · Λ′(s₀, χ⁻¹)`.

So the functional equation carries the DERIVATIVE at an event of the fiber `χ⁻¹` to the derivative at the
mirror event of the fiber `χ`, rotated by the root number and the conductor clock `N^{s₀−½}` — on the line a
unit phasor `N^{iγ}`.  No Schwarz reflection is used (Mathlib has none for `completedLFunction`); this is
the functional-equation half of the 652 identity `ζ′(ρ) = −χ(ρ)·ζ′(ρ)‾`, valid for every GRH fiber and at
every zero, on the line or not.  For `N = 1` it is `ξ′(1 − s) = −ξ′(s)`.
-/

open Complex DirichletCharacter

namespace CriticalLinePhasor.MirrorDerivative

variable {N : ℕ} [NeZero N]

/-- The functional equation, differentiated. -/
theorem deriv_completedLFunction_one_sub {χ : DirichletCharacter ℂ N} (hχ : IsPrimitive χ) (s : ℂ)
    (h0 : s ≠ 0 ∨ N ≠ 1) (h1 : s ≠ 1 ∨ χ⁻¹ ≠ 1) (h0' : 1 - s ≠ 0 ∨ N ≠ 1) (h1' : 1 - s ≠ 1 ∨ χ ≠ 1) :
    deriv (completedLFunction χ) (1 - s)
      = -((N : ℂ) ^ (s - 1 / 2) * Complex.log N * rootNumber χ * completedLFunction χ⁻¹ s
          + (N : ℂ) ^ (s - 1 / 2) * rootNumber χ * deriv (completedLFunction χ⁻¹) s) := by
  have hL : HasDerivAt (fun s => completedLFunction χ (1 - s))
      (-(deriv (completedLFunction χ) (1 - s))) s := by
    have hd := (differentiableAt_completedLFunction χ (1 - s) h0' h1').hasDerivAt
    have h1s : HasDerivAt (fun s : ℂ => 1 - s) (-1) s := (hasDerivAt_id s).const_sub 1
    exact (hd.comp s h1s).congr_deriv (by ring)
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hp : HasDerivAt (fun s : ℂ => (N : ℂ) ^ (s - 1 / 2))
      ((N : ℂ) ^ (s - 1 / 2) * Complex.log N * 1) s :=
    ((hasDerivAt_id s).sub_const (1 / 2)).const_cpow (Or.inl hN)
  have hΛ := (differentiableAt_completedLFunction χ⁻¹ s h0 h1).hasDerivAt
  have hR := (hp.mul_const (rootNumber χ)).mul hΛ
  have hfun : (fun s => completedLFunction χ (1 - s))
      = fun s => (N : ℂ) ^ (s - 1 / 2) * rootNumber χ * completedLFunction χ⁻¹ s := by
    funext s; exact hχ.completedLFunction_one_sub s
  rw [hfun] at hL
  have := hL.unique hR
  linear_combination -this

/-- **Mirror transport at an event.**  A zero `s₀` of `Λ(·, χ⁻¹)` is mirrored to a zero `1 − s₀` of
`Λ(·, χ)`, and the derivatives are transported by `−N^{s₀−½} ε(χ)`. -/
theorem mirror_event {χ : DirichletCharacter ℂ N} (hχ : IsPrimitive χ) {s₀ : ℂ}
    (h0 : s₀ ≠ 0 ∨ N ≠ 1) (h1 : s₀ ≠ 1 ∨ χ⁻¹ ≠ 1) (h0' : 1 - s₀ ≠ 0 ∨ N ≠ 1) (h1' : 1 - s₀ ≠ 1 ∨ χ ≠ 1)
    (hz : completedLFunction χ⁻¹ s₀ = 0) :
    completedLFunction χ (1 - s₀) = 0 ∧
      deriv (completedLFunction χ) (1 - s₀)
        = -((N : ℂ) ^ (s₀ - 1 / 2) * rootNumber χ * deriv (completedLFunction χ⁻¹) s₀) := by
  refine ⟨by rw [hχ.completedLFunction_one_sub, hz, mul_zero], ?_⟩
  rw [deriv_completedLFunction_one_sub hχ s₀ h0 h1 h0' h1', hz]
  ring

/-- On the line the conductor clock is a unit phasor. -/
theorem norm_conductor_clock {s₀ : ℂ} (hs : s₀.re = 1 / 2) :
    ‖(N : ℂ) ^ (s₀ - 1 / 2)‖ = 1 := by
  rw [Complex.norm_natCast_cpow_of_pos (NeZero.pos N)]
  have : (s₀ - 1 / 2).re = 0 := by simp [hs]
  rw [this, Real.rpow_zero]

/-- On the line the mirror transport preserves the derivative's magnitude up to `‖ε(χ)‖`. -/
theorem norm_deriv_mirror_event {χ : DirichletCharacter ℂ N} (hχ : IsPrimitive χ) {s₀ : ℂ}
    (hs : s₀.re = 1 / 2)
    (h0 : s₀ ≠ 0 ∨ N ≠ 1) (h1 : s₀ ≠ 1 ∨ χ⁻¹ ≠ 1) (h0' : 1 - s₀ ≠ 0 ∨ N ≠ 1) (h1' : 1 - s₀ ≠ 1 ∨ χ ≠ 1)
    (hz : completedLFunction χ⁻¹ s₀ = 0) :
    ‖deriv (completedLFunction χ) (1 - s₀)‖
      = ‖rootNumber χ‖ * ‖deriv (completedLFunction χ⁻¹) s₀‖ := by
  rw [(mirror_event hχ h0 h1 h0' h1' hz).2, norm_neg, norm_mul, norm_mul, norm_conductor_clock hs,
    one_mul]

/-- Real (quadratic) fibers, `χ⁻¹ = χ`: the transport acts within one fiber. -/
theorem mirror_event_self {χ : DirichletCharacter ℂ N} (hχ : IsPrimitive χ) (hself : χ⁻¹ = χ) {s₀ : ℂ}
    (h0 : s₀ ≠ 0 ∨ N ≠ 1) (h1 : s₀ ≠ 1 ∨ χ ≠ 1) (h0' : 1 - s₀ ≠ 0 ∨ N ≠ 1) (h1' : 1 - s₀ ≠ 1 ∨ χ ≠ 1)
    (hz : completedLFunction χ s₀ = 0) :
    deriv (completedLFunction χ) (1 - s₀)
      = -((N : ℂ) ^ (s₀ - 1 / 2) * rootNumber χ * deriv (completedLFunction χ) s₀) := by
  have h1i : s₀ ≠ 1 ∨ χ⁻¹ ≠ 1 := by rw [hself]; exact h1
  have hzi : completedLFunction χ⁻¹ s₀ = 0 := by rw [hself]; exact hz
  have := (mirror_event hχ h0 h1i h0' h1' hzi).2
  rw [hself] at this
  exact this

/-- `Λ = Λ₀ − 1/s − 1/(1−s)` is differentiable away from the poles. -/
theorem differentiableAt_completedRiemannZeta' {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    DifferentiableAt ℂ completedRiemannZeta s := by
  have hfun : completedRiemannZeta
      = fun s => completedRiemannZeta₀ s - 1 / s - 1 / (1 - s) := by
    funext s; exact completedRiemannZeta_eq s
  rw [hfun]
  have h1s : (1 : ℂ) - s ≠ 0 := fun h => h1 (by linear_combination -h)
  exact ((differentiable_completedZeta₀ s).sub
    ((differentiableAt_const _).div differentiableAt_id h0)).sub
    ((differentiableAt_const _).div ((differentiableAt_const _).sub differentiableAt_id) h1s)

/-- `N = 1`: `ξ′(1 − s) = −ξ′(s)` away from the poles (from `completedRiemannZeta_one_sub`). -/
theorem deriv_completedRiemannZeta_one_sub {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    deriv completedRiemannZeta (1 - s) = -deriv completedRiemannZeta s := by
  have h0' : 1 - s ≠ 0 := fun h => h1 (by linear_combination -h)
  have h1' : 1 - s ≠ 1 := fun h => h0 (by linear_combination -h)
  have hd := (differentiableAt_completedRiemannZeta' h0' h1').hasDerivAt
  have h1s : HasDerivAt (fun s : ℂ => 1 - s) (-1) s := (hasDerivAt_id s).const_sub 1
  have hL : HasDerivAt (fun s => completedRiemannZeta (1 - s))
      (-(deriv completedRiemannZeta (1 - s))) s := (hd.comp s h1s).congr_deriv (by ring)
  have hfun : (fun s => completedRiemannZeta (1 - s)) = completedRiemannZeta := by
    funext s; exact completedRiemannZeta_one_sub s
  rw [hfun] at hL
  have := hL.unique (differentiableAt_completedRiemannZeta' h0 h1).hasDerivAt
  linear_combination -this

end CriticalLinePhasor.MirrorDerivative

#print axioms CriticalLinePhasor.MirrorDerivative.mirror_event
#print axioms CriticalLinePhasor.MirrorDerivative.norm_deriv_mirror_event
#print axioms CriticalLinePhasor.MirrorDerivative.deriv_completedRiemannZeta_one_sub
