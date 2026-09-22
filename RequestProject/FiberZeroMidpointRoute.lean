import RequestProject.MidpointDescent
import RequestProject.ZetaZeroNative3DSourceTransfer
import RequestProject.UnitMidpoint

/-!
# The route `L = 0 ⟹ fiber3D = 0 ⟹ involution ⟹ midpoint ⟹ descent ⟹ Re s = ½`, walked

Every link of the advocate's route is compiled here except one, and that one is isolated as a
single proposition about the three-dimensional fiber alone (`OneVanishingPerHeight3D`), with the
door from it to the line, and its converse — so that it is exactly the missing content, neither
stronger nor weaker.

The links.

* `fiber3D_vanishes_iff_zero` — in the strip, `ζ(σ+iy) = 0 ⟺ laneChart3D σ y = 0`: a zero of
  the one-dimensional function IS a vanishing of the three-dimensional fiber's chart
  (`zeta_zero_iff_bank_mem_ker` read through `laneChart3D_eq`).
* `fiber3D_vanishes_at_partner` — **the involution.**  A fiber vanishing at abscissa `σ` is a
  fiber vanishing at abscissa `1 − σ` at the SAME carrier height `y`: the functional equation
  together with Schwarz reflection (`one_sub_conj_mem_nontrivialZeros`) pairs the fibers
  `phasor3D χ₂ σ y` and `phasor3D χ₂ (1−σ) y`; their 3-D magnitudes multiply to `n⁻¹` at every
  site (`paired_radialMagnitude_product`), and they coincide iff `σ = ½`
  (`reflected_radialMagnitude_eq_iff_carrierScaleBalanced`).
* `OneVanishingPerHeight3D` — **the one missing implication**: at one carrier height the fiber
  vanishes for at most one abscissa.  No `½` in it.
* `midpoint_of_fiber3D_zero` — under it, a vanishing is a fixed point of the involution
  `σ ↦ 1 − σ`, whose fixed locus is `½` (`affine_reflection_fixed_iff`): the midpoint is forced.
* `fiber_zero_descends_to_line` — the composite in the six-step form: the vanishing lies on the
  3-D midpoint locus (`midpointFocalZero`), descends to `ζ(½+iy) = 0` (`midpoint_zero_descends`),
  and its readout has abscissa `½` (`descend_re`).
* `rh_of_oneVanishingPerHeight3D` / `oneVanishingPerHeight3D_of_rh` — the proposition is
  exactly the target: it implies the line and is implied by it.  So no compiled result can
  discharge it unless that result already proves the line — the guard of rule 11.
* The route compiled unconditionally in the certified window `|y| ≤ 1269/2` is in
  `FiberZeroMidpointWindow.lean` (it imports the station ladder, which this file does not).

Every statement is unconditional; the only hypothesis anywhere is the named proposition.
-/

open CriticalLinePhasor

noncomputable section

namespace CarrierReadout

/-! ### Link 1: a zero of the function is a vanishing of the 3-D fiber's chart -/

theorem re_add_mul_I (σ y : ℝ) : ((σ : ℂ) + (y : ℂ) * Complex.I).re = σ := by
  simp [Complex.add_re, Complex.mul_re]

theorem im_add_mul_I (σ y : ℝ) : ((σ : ℂ) + (y : ℂ) * Complex.I).im = y := by
  simp [Complex.add_im, Complex.mul_im]

/-- **A zero of `ζ` in the strip is exactly a vanishing of the three-dimensional fiber's chart**
at the same `(σ, y)`. -/
theorem fiber3D_vanishes_iff_zero {σ y : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    riemannZeta ((σ : ℂ) + (y : ℂ) * Complex.I) = 0 ↔ laneChart3D σ y = 0 := by
  rw [laneChart3D_eq]
  exact zeta_zero_iff_bank_mem_ker (by rw [re_add_mul_I]; exact hσ0)
    (by rw [re_add_mul_I]; exact hσ1)

theorem fiber3D_vanishes_of_zero {σ y : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (hζ : riemannZeta ((σ : ℂ) + (y : ℂ) * Complex.I) = 0) : laneChart3D σ y = 0 :=
  (fiber3D_vanishes_iff_zero hσ0 hσ1).mp hζ

theorem mem_nontrivialZeros_of_fiber3D_zero {σ y : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (h : laneChart3D σ y = 0) : ((σ : ℂ) + (y : ℂ) * Complex.I) ∈ ZD.NontrivialZeros :=
  ⟨by rw [re_add_mul_I]; exact hσ0, by rw [re_add_mul_I]; exact hσ1,
    (fiber3D_vanishes_iff_zero hσ0 hσ1).mpr h⟩

/-! ### Link 2: the involution — the partner fiber vanishes at the same carrier height -/

theorem one_sub_conj_eq (σ y : ℝ) :
    1 - (starRingEnd ℂ) ((σ : ℂ) + (y : ℂ) * Complex.I)
      = ((1 - σ : ℝ) : ℂ) + (y : ℂ) * Complex.I := by
  rw [map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- **The involution.**  A vanishing of the 3-D fiber at abscissa `σ` is a vanishing at abscissa
`1 − σ`, at the same carrier height `y`.  (Functional equation + Schwarz reflection, through
`one_sub_conj_mem_nontrivialZeros`.) -/
theorem fiber3D_vanishes_at_partner {σ y : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (h : laneChart3D σ y = 0) : laneChart3D (1 - σ) y = 0 := by
  have hmem := ContourArgument.one_sub_conj_mem_nontrivialZeros
    (mem_nontrivialZeros_of_fiber3D_zero hσ0 hσ1 h)
  rw [one_sub_conj_eq] at hmem
  exact fiber3D_vanishes_of_zero (by linarith) (by linarith) hmem.2.2

/-- The pair `(σ, y)`, `(1 − σ, y)` is a single vanishing iff `σ = ½`: the fixed locus of the
involution `σ ↦ 1 − σ` is the midpoint (`affine_reflection_fixed_iff` at unit `1`). -/
theorem partner_eq_self_iff (σ : ℝ) : 1 - σ = σ ↔ σ = 1 / 2 :=
  UnitMidpoint.affine_reflection_fixed_iff 1 σ

/-! ### The one missing implication, and the door from it -/

/-- **ONE VANISHING PER HEIGHT of the three-dimensional fiber.**  At one carrier height `y` the
fiber's chart vanishes for at most one abscissa in the strip.  This is the single proposition the
route below consumes; no `½` occurs in it. -/
def OneVanishingPerHeight3D : Prop :=
  ∀ (y σ₁ σ₂ : ℝ), 0 < σ₁ → σ₁ < 1 → 0 < σ₂ → σ₂ < 1 →
    laneChart3D σ₁ y = 0 → laneChart3D σ₂ y = 0 → σ₁ = σ₂

/-- **The midpoint is forced.**  Under one vanishing per height, a fiber vanishing at `(σ, y)` is
a fixed point of the involution `σ ↦ 1 − σ`, hence `σ = ½`. -/
theorem midpoint_of_fiber3D_zero (h1 : OneVanishingPerHeight3D) {σ y : ℝ}
    (hσ0 : 0 < σ) (hσ1 : σ < 1) (h : laneChart3D σ y = 0) : σ = 1 / 2 := by
  have hp := fiber3D_vanishes_at_partner hσ0 hσ1 h
  have hfix : σ = 1 - σ := h1 y σ (1 - σ) hσ0 hσ1 (by linarith) (by linarith) h hp
  exact (partner_eq_self_iff σ).mp hfix.symm

/-- **The six-step composite.**  Under one vanishing per height: a vanishing of the 3-D fiber at
`(σ, y)` in the strip lies on the 3-D midpoint locus, descends to a zero of `ζ` at `½ + iy`, and
its readout has abscissa `½`. -/
theorem fiber_zero_descends_to_line (h1 : OneVanishingPerHeight3D) {σ y : ℝ}
    (hσ0 : 0 < σ) (hσ1 : σ < 1) (h : laneChart3D σ y = 0) :
    σ = 1 / 2 ∧ midpointFocalZero y ∧ riemannZeta (descend y) = 0 ∧ (descend y).re = 1 / 2 := by
  have hσ := midpoint_of_fiber3D_zero h1 hσ0 hσ1 h
  subst hσ
  exact ⟨rfl, h, (midpoint_zero_descends y).mp h, descend_re y⟩

/-- **RH from one vanishing per height of the 3-D fiber.** -/
theorem rh_of_oneVanishingPerHeight3D (h1 : OneVanishingPerHeight3D) :
    ∀ ρ ∈ ZD.NontrivialZeros, ρ.re = 1 / 2 := by
  rintro ρ ⟨h0, hlt, hζ⟩
  have hρ : ρ = (ρ.re : ℂ) + (ρ.im : ℂ) * Complex.I := (Complex.re_add_im ρ).symm
  rw [hρ] at hζ
  exact midpoint_of_fiber3D_zero h1 h0 hlt (fiber3D_vanishes_of_zero h0 hlt hζ)

/-- **The converse: the proposition is exactly the target, not stronger.**  If every nontrivial
zero is on the line, the 3-D fiber vanishes at most once per height. -/
theorem oneVanishingPerHeight3D_of_rh (hRH : ∀ ρ ∈ ZD.NontrivialZeros, ρ.re = 1 / 2) :
    OneVanishingPerHeight3D := by
  intro y σ₁ σ₂ h10 h11 h20 h21 hz1 hz2
  have e1 := hRH _ (mem_nontrivialZeros_of_fiber3D_zero h10 h11 hz1)
  have e2 := hRH _ (mem_nontrivialZeros_of_fiber3D_zero h20 h21 hz2)
  rw [re_add_mul_I] at e1 e2
  linarith

theorem oneVanishingPerHeight3D_iff_rh :
    OneVanishingPerHeight3D ↔ ∀ ρ ∈ ZD.NontrivialZeros, ρ.re = 1 / 2 :=
  ⟨rh_of_oneVanishingPerHeight3D, oneVanishingPerHeight3D_of_rh⟩

end CarrierReadout
