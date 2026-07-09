import Mathlib

/-!
# Reachable independent stage: the dual helix supplies two independent correction directions

`ForcibleClosure.residual_forcible` closes any cell residual *given* two `ℝ`-linearly-independent warp
correction directions `u, v`.  For the dual carrier those directions are the two lanes `e^{±iφ(y)}` of
the helix; a complex number and its conjugate are `ℝ`-independent iff off the real/imaginary axes, i.e.
iff `sin(2 φ(y)) ≠ 0`.  This file discharges that hypothesis unconditionally on the nontrivial source
class, from the *basic* structure of the carrier rather than any genericity/measure argument:

* `exists_sin_two_phi_ne_zero` — a continuous, non-constant lane phase `φ : ℝ → ℝ` has
  `sin(2 φ y) ≠ 0` at some carrier height `y`.  Proof: if `sin(2φ) ≡ 0` then `φ` maps the connected,
  complete line `ℝ` (`0→∞` on both lanes) into the countable set `(π/2)·ℤ`, so its connected range is
  a subsingleton and `φ` is constant — excluded by nontriviality.
* `lanes_linearIndependent` — `sin(2 φ) ≠ 0 ⇒ e^{iφ}, e^{-iφ}` are `ℝ`-linearly independent.
* `reachable_independent_stage` — hence a complete dual carrier with a continuous nontrivial clock
  admits a stage with two `ℝ`-independent lane directions, exactly the hypothesis of `residual_forcible`.

No `sorry`, no `axiom`.
-/

open scoped Real
open Complex

namespace CriticalLinePhasor.CarrierReachability

/-- The zeros of `c ↦ sin (2 c)` form the countable set `(π/2)·ℤ`. -/
theorem countable_sin_two_zeros : {c : ℝ | Real.sin (2 * c) = 0}.Countable := by
  refine (Set.countable_range (fun k : ℤ => (k : ℝ) * π / 2)).mono ?_
  intro c hc
  simp only [Set.mem_setOf_eq] at hc
  rw [Real.sin_eq_zero_iff] at hc
  obtain ⟨n, hn⟩ := hc
  exact ⟨n, by linarith [hn]⟩

/-- A countable preconnected subset of `ℝ` is a subsingleton. -/
theorem subsingleton_of_countable_preconnected {s : Set ℝ}
    (hc : s.Countable) (hp : IsPreconnected s) : s.Subsingleton := by
  by_contra h
  rw [Set.not_subsingleton_iff] at h
  obtain ⟨a, ha, b, hb, hab⟩ := h
  have hoc : s.OrdConnected := hp.ordConnected
  rcases lt_or_gt_of_ne hab with hlt | hlt
  · have : (Set.Icc a b).Countable := hc.mono (hoc.out ha hb)
    rw [Cardinal.Real.Icc_countable_iff] at this; linarith
  · have : (Set.Icc b a).Countable := hc.mono (hoc.out hb ha)
    rw [Cardinal.Real.Icc_countable_iff] at this; linarith

/-- **Reachable independent stage (core).** A continuous, non-constant lane phase attains a carrier
height where `sin(2 φ) ≠ 0`. -/
theorem exists_sin_two_phi_ne_zero {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hnc : ¬ ∀ x, φ x = φ 0) : ∃ y, Real.sin (2 * φ y) ≠ 0 := by
  by_contra h
  push_neg at h
  refine hnc (fun x => ?_)
  have hsub : Set.range φ ⊆ {c : ℝ | Real.sin (2 * c) = 0} := by
    rintro _ ⟨y, rfl⟩; exact h y
  have hss : (Set.range φ).Subsingleton :=
    subsingleton_of_countable_preconnected (countable_sin_two_zeros.mono hsub)
      (isConnected_range hφ).isPreconnected
  exact hss (Set.mem_range_self x) (Set.mem_range_self 0)

/-- **Independent lanes.** When `sin(2 φ) ≠ 0`, the two conjugate lane directions `e^{±iφ}` are
`ℝ`-linearly independent in `ℂ`. -/
theorem lanes_linearIndependent {φ : ℝ} (h : Real.sin (2 * φ) ≠ 0) :
    LinearIndependent ℝ ![Complex.exp (↑φ * I), Complex.exp (-↑φ * I)] := by
  have hsc : Real.sin φ ≠ 0 ∧ Real.cos φ ≠ 0 := by
    rw [Real.sin_two_mul] at h
    refine ⟨fun hs => h ?_, fun hcs => h ?_⟩
    · rw [hs]; ring
    · rw [hcs]; ring
  obtain ⟨hs, hcos⟩ := hsc
  have hveq : (-↑φ * I : ℂ) = ↑(-φ) * I := by push_cast; ring
  have hure : (Complex.exp (↑φ * I)).re = Real.cos φ := Complex.exp_ofReal_mul_I_re φ
  have huim : (Complex.exp (↑φ * I)).im = Real.sin φ := Complex.exp_ofReal_mul_I_im φ
  have hvre : (Complex.exp (-↑φ * I)).re = Real.cos φ := by
    rw [hveq, Complex.exp_ofReal_mul_I_re, Real.cos_neg]
  have hvim : (Complex.exp (-↑φ * I)).im = -Real.sin φ := by
    rw [hveq, Complex.exp_ofReal_mul_I_im, Real.sin_neg]
  rw [LinearIndependent.pair_iff]
  intro a b hab
  have hre : (a + b) * Real.cos φ = 0 := by
    have h0 := congrArg Complex.re hab
    simp only [Complex.add_re, Complex.zero_re, Complex.real_smul, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, hure, hvre] at h0
    linear_combination h0
  have him : (a - b) * Real.sin φ = 0 := by
    have h0 := congrArg Complex.im hab
    simp only [Complex.add_im, Complex.zero_im, Complex.real_smul, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, huim, hvim] at h0
    linear_combination h0
  have h1 : a + b = 0 := (mul_eq_zero.mp hre).resolve_right hcos
  have h2 : a - b = 0 := (mul_eq_zero.mp him).resolve_right hs
  constructor <;> linarith

/-- **Reachable independent stage.**  A *complete* dual carrier (lane phase `φ` continuous on all of
`ℝ`, `0→∞` on both lanes) carrying a *nontrivial* (non-constant) structured clock admits a carrier
height at which the two lane directions `e^{±iφ}` are `ℝ`-linearly independent — the exact hypothesis
`ForcibleClosure.residual_forcible` consumes.  Unconditional; no genericity or measure argument. -/
theorem reachable_independent_stage {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hnc : ¬ ∀ x, φ x = φ 0) :
    ∃ y, LinearIndependent ℝ ![Complex.exp (↑(φ y) * I), Complex.exp (-↑(φ y) * I)] := by
  obtain ⟨y, hy⟩ := exists_sin_two_phi_ne_zero hφ hnc
  exact ⟨y, lanes_linearIndependent hy⟩

end CriticalLinePhasor.CarrierReachability
