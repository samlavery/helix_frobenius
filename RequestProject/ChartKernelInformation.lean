import RequestProject.PartnerPhasorRigidity

/-!
# Above the chart: what the projection `(phasor3D χ₂ σ y n)_n ↦ laneChart3D σ y` forgets

At ONE height `y` the full configuration is the sequence `v_n = phasor3D χ₂ σ y (n+1)` in
`ℂ × ℝ`; the chart is the paired sum of its plane parts.  This file computes, unconditionally,
what lies above the chart and what chart vanishing does and does not impose on it.

* **P2 — the partner configuration is a function of the configuration**
  (`phasor3D_partner_rescale`): `phasor3D χ₂ (1−σ) y (n+1) = ((n+1)^{2σ−1}·plane(v_n), 0)`, the
  sitewise reciprocal deformation with the same phases.  It carries no independent full-3-D
  information; its chart vanishing follows (`partner_vanishing_iff`, P1).
* **The third coordinate is identically zero** on the lane fiber and so is its paired sum
  (`massChart3D_eq_zero`): the unprojected 3-D sum is `(laneChart3D σ y, 0)`.
* **The radial moments before projection are the horizontal profile**
  (`deformationMoment_eq`): weighting the configuration by `(n+1)^{−ε}` and summing gives
  `laneChart3D (σ+ε) y`.  So the configuration at height `y` carries the whole profile
  `σ' ↦ laneChart3D σ' y`; chart vanishing at `σ` is the statement that this profile has a zero
  at `σ`, and nothing else about it.
* **Cross products of successive phasors** (`cross_succ`): closed form
  `((n+1)(n+2))^{−σ}·sin(y·log((n+2)/(n+1)))` — a function of `(σ, y)` the chart value never
  enters.
* **The exact single-height content of chart vanishing, read on the midpoint state**
  (`chart_zero_iff_moments`): for `|δ| < ½`, `laneChart3D (½+δ) y = 0` iff the midpoint
  configuration `m(y)` is annihilated by BOTH the `cosh(δ·log)`- and the `sinh(δ·log)`-weighted
  paired sums.  This uses P1 (the partner adds no chart equation) and the even/odd split; it is
  exactly what a vanishing at radial deformation `δ` says about the undeformed (admissible) state.
* **The forced `E = E_mid` relation** (`midpoint_chart_of_vanishing`): from chart vanishing at
  `½+δ` ALONE, the midpoint chart at the same height equals `−½` the asymmetry-energy sum.

No `axiom`, no `sorry`.
-/

open CriticalLinePhasor
open scoped BigOperators

noncomputable section

namespace CarrierReadout

/-! ### P2: the partner configuration is the sitewise reciprocal deformation of the configuration -/

/-- The plane part of the partner phasor is `(n+1)^{2σ−1}` times the plane part of the phasor:
same phase, reciprocal radial deformation. -/
theorem plane_partner_rescale (σ y : ℝ) (n : ℕ) :
    Phasor3D.plane (Phasor3D.phasor3D chi2 (1 - σ) y (n + 1))
      = ((((n : ℝ) + 1) ^ (2 * σ - 1) : ℝ) : ℂ)
          * Phasor3D.plane (Phasor3D.phasor3D chi2 σ y (n + 1)) := by
  rw [plane_chi2_eq, plane_chi2_eq]
  have : ((n : ℝ) + 1) ^ (-(1 - σ)) = ((n : ℝ) + 1) ^ (2 * σ - 1) * ((n : ℝ) + 1) ^ (-σ) := by
    rw [← Real.rpow_add (site_pos n)]; congr 1; ring
  rw [this]; push_cast; ring

/-- **P2.**  The full 3-D partner configuration is a function of the full 3-D configuration:
`phasor3D χ₂ (1−σ) y (n+1) = ((n+1)^{2σ−1} · plane(v_n), 0)`. -/
theorem phasor3D_partner_rescale (σ y : ℝ) (n : ℕ) :
    Phasor3D.phasor3D chi2 (1 - σ) y (n + 1)
      = (((((n : ℝ) + 1) ^ (2 * σ - 1) : ℝ) : ℂ)
          * Phasor3D.plane (Phasor3D.phasor3D chi2 σ y (n + 1)), 0) := by
  refine Prod.ext ?_ ?_
  · exact plane_partner_rescale σ y n
  · exact massAxis_chi2 (1 - σ) y n

/-! ### The kernel of the projection: the third coordinate and the unprojected sum -/

/-- The paired sum of the mass-axis coordinates. -/
def massChart3D (σ y : ℝ) : ℝ :=
  ∑' k : ℕ, (Phasor3D.massAxis (Phasor3D.phasor3D chi2 σ y (2 * k + 1))
    + Phasor3D.massAxis (Phasor3D.phasor3D chi2 σ y (2 * k + 2)))

/-- **The third coordinate carries nothing**: the lane fiber has no mass, so the unprojected 3-D
sum is `(laneChart3D σ y, 0)` — the projection forgets no coordinate of the sum. -/
theorem massChart3D_eq_zero (σ y : ℝ) : massChart3D σ y = 0 := by
  unfold massChart3D
  have h : ∀ k : ℕ, Phasor3D.massAxis (Phasor3D.phasor3D chi2 σ y (2 * k + 1))
      + Phasor3D.massAxis (Phasor3D.phasor3D chi2 σ y (2 * k + 2)) = 0 := by
    intro k
    rw [show 2 * k + 2 = 2 * k + 1 + 1 by ring, massAxis_chi2, massAxis_chi2, add_zero]
  simp_rw [h]
  exact tsum_zero

/-! ### The radial moments before projection are the horizontal profile -/

/-- The `ε`-th radial moment of the configuration at `(σ, y)`: the paired sum of the plane parts
weighted by the deformation `(n+1)^{−ε}` — a functional of the full configuration, before
projection. -/
def deformationMoment (σ y ε : ℝ) : ℂ :=
  ∑' k : ℕ, (((deformation ε (2 * k) : ℝ) : ℂ)
      * Phasor3D.plane (Phasor3D.phasor3D chi2 σ y (2 * k + 1))
    + ((deformation ε (2 * k + 1) : ℝ) : ℂ)
      * Phasor3D.plane (Phasor3D.phasor3D chi2 σ y (2 * k + 2)))

/-- **What survives upstairs is the horizontal profile**: the `ε`-th radial moment of the
configuration at `(σ, y)` is the chart at `(σ + ε, y)`.  The chart itself is the `ε = 0` moment. -/
theorem deformationMoment_eq (σ y ε : ℝ) : deformationMoment σ y ε = laneChart3D (σ + ε) y := by
  unfold deformationMoment
  rw [laneChart3D_eq_tsum]
  refine tsum_congr fun k => ?_
  unfold laneSummand
  rw [show 2 * k + 2 = 2 * k + 1 + 1 by ring, plane_chi2_eq σ y (2 * k), plane_chi2_eq σ y (2 * k + 1),
    plane_chi2_eq (σ + ε) y (2 * k), plane_chi2_eq (σ + ε) y (2 * k + 1)]
  unfold deformation
  rw [show -(σ + ε) = -ε + -σ by ring, Real.rpow_add (site_pos (2 * k)),
    Real.rpow_add (site_pos (2 * k + 1))]
  push_cast
  ring

theorem deformationMoment_zero (σ y : ℝ) : deformationMoment σ y 0 = laneChart3D σ y := by
  rw [deformationMoment_eq, add_zero]

/-! ### Cross products of successive phasors: chart-free -/

theorem chi2_succ_mul_succ (n : ℕ) : chi2 (n + 1) * chi2 (n + 2) = -1 := by
  unfold chi2
  rcases Nat.mod_two_eq_zero_or_one (n + 1) with h | h
  · have h' : (n + 2) % 2 = 1 := by omega
    simp [h, h']
  · have h' : (n + 2) % 2 = 0 := by omega
    simp [h, h']

theorem conj_mellinSpin_mul (y : ℝ) (a b : ℕ) :
    (starRingEnd ℂ) (LFunctionPhasor.mellinSpin y a) * LFunctionPhasor.mellinSpin y b
      = Complex.exp (((y * (Real.log a - Real.log b) : ℝ) : ℂ) * Complex.I) := by
  rw [← mellinSpin_neg]
  unfold LFunctionPhasor.mellinSpin
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- **The cross product (oriented area element) of successive phasors** in closed form:
`Im(conj(v_n)·v_{n+1}) = ((n+1)(n+2))^{−σ} · sin(y·(log(n+2) − log(n+1)))`.  A function of `(σ, y)`
in which the chart value never enters. -/
theorem cross_succ (σ y : ℝ) (n : ℕ) :
    ((starRingEnd ℂ) (Phasor3D.plane (Phasor3D.phasor3D chi2 σ y (n + 1)))
        * Phasor3D.plane (Phasor3D.phasor3D chi2 σ y (n + 2))).im
      = (((n : ℝ) + 1) ^ (-σ) * ((n : ℝ) + 2) ^ (-σ))
          * Real.sin (y * (Real.log ((n : ℝ) + 2) - Real.log ((n : ℝ) + 1))) := by
  have h2 : n + 2 = (n + 1) + 1 := by ring
  rw [h2, plane_chi2_eq, plane_chi2_eq]
  have hc : ∀ m, (starRingEnd ℂ) (chi2 m) = chi2 m := by
    intro m; unfold chi2; split_ifs <;> simp
  rw [map_mul, map_mul, hc, Complex.conj_ofReal]
  have hcast : (((n + 1 : ℕ) : ℝ) + 1) = (n : ℝ) + 2 := by push_cast; ring
  have hprod : chi2 (n + 1) * ((((n : ℝ) + 1) ^ (-σ) : ℝ) : ℂ)
        * (starRingEnd ℂ) (LFunctionPhasor.mellinSpin y (n + 1))
        * (chi2 (n + 1 + 1) * (((((n + 1 : ℕ) : ℝ) + 1) ^ (-σ) : ℝ) : ℂ)
          * LFunctionPhasor.mellinSpin y (n + 1 + 1))
      = ((-(((n : ℝ) + 1) ^ (-σ) * ((n : ℝ) + 2) ^ (-σ)) : ℝ) : ℂ)
          * ((starRingEnd ℂ) (LFunctionPhasor.mellinSpin y (n + 1))
            * LFunctionPhasor.mellinSpin y (n + 1 + 1)) := by
    have := chi2_succ_mul_succ n
    rw [show n + 1 + 1 = n + 2 by ring, hcast]
    push_cast
    linear_combination (((((n : ℝ) + 1) ^ (-σ) : ℝ) : ℂ) * ((((n : ℝ) + 2) ^ (-σ) : ℝ) : ℂ)
      * ((starRingEnd ℂ) (LFunctionPhasor.mellinSpin y (n + 1))
        * LFunctionPhasor.mellinSpin y (n + 2))) * this
  rw [hprod, conj_mellinSpin_mul, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]
  have hlog : Real.log ((n + 1 : ℕ) : ℝ) - Real.log ((n + 1 + 1 : ℕ) : ℝ)
      = -(Real.log ((n : ℝ) + 2) - Real.log ((n : ℝ) + 1)) := by
    push_cast; ring
  rw [hlog, mul_neg, Real.sin_neg]
  ring

/-! ### The exact single-height content of chart vanishing, read on the midpoint state -/

/-- The `cosh(δ·log)`-weighted paired sum of the midpoint configuration. -/
def coshMoment (δ y : ℝ) : ℂ :=
  ∑' k : ℕ, ((Real.cosh (δ * Real.log (((2 * k : ℕ) : ℝ) + 1)) : ℂ)
      * Phasor3D.plane (Phasor3D.phasor3D chi2 (1 / 2) y (2 * k + 1))
    + (Real.cosh (δ * Real.log (((2 * k + 1 : ℕ) : ℝ) + 1)) : ℂ)
      * Phasor3D.plane (Phasor3D.phasor3D chi2 (1 / 2) y (2 * k + 2)))

/-- The `sinh(δ·log)`-weighted paired sum of the midpoint configuration. -/
def sinhMoment (δ y : ℝ) : ℂ :=
  ∑' k : ℕ, ((Real.sinh (δ * Real.log (((2 * k : ℕ) : ℝ) + 1)) : ℂ)
      * Phasor3D.plane (Phasor3D.phasor3D chi2 (1 / 2) y (2 * k + 1))
    + (Real.sinh (δ * Real.log (((2 * k + 1 : ℕ) : ℝ) + 1)) : ℂ)
      * Phasor3D.plane (Phasor3D.phasor3D chi2 (1 / 2) y (2 * k + 2)))

/-- The even part of the deformation is the cosh-moment of the midpoint state. -/
theorem evenChart_eq_coshMoment {δ : ℝ} (hδ : |δ| < 1 / 2) (y : ℝ) :
    evenChart δ y = coshMoment δ y := by
  have s1 := laneSummand_summable (half_add_pos hδ) y
  have s2 := laneSummand_summable (half_sub_pos hδ) y
  unfold evenChart coshMoment
  rw [laneChart3D_eq_tsum, laneChart3D_eq_tsum, ← s1.tsum_add s2, div_eq_mul_inv,
    ← tsum_mul_right]
  refine tsum_congr fun k => ?_
  unfold laneSummand
  rw [show 2 * k + 2 = 2 * k + 1 + 1 by ring]
  have e1 := plane_partner_add δ y (2 * k)
  have e2 := plane_partner_add δ y (2 * k + 1)
  rw [deformation_add_neg_eq_cosh] at e1 e2
  push_cast at e1 e2 ⊢
  linear_combination (1 / 2 : ℂ) * (e1 + e2)

/-- The odd part of the deformation is minus the sinh-moment of the midpoint state. -/
theorem oddChart_eq_neg_sinhMoment {δ : ℝ} (hδ : |δ| < 1 / 2) (y : ℝ) :
    oddChart δ y = -sinhMoment δ y := by
  have s1 := laneSummand_summable (half_add_pos hδ) y
  have s2 := laneSummand_summable (half_sub_pos hδ) y
  unfold oddChart sinhMoment
  rw [laneChart3D_eq_tsum, laneChart3D_eq_tsum, ← s1.tsum_sub s2, div_eq_mul_inv,
    ← tsum_mul_right, ← tsum_neg]
  refine tsum_congr fun k => ?_
  unfold laneSummand
  rw [show 2 * k + 2 = 2 * k + 1 + 1 by ring]
  have e1 := plane_partner_sub δ y (2 * k)
  have e2 := plane_partner_sub δ y (2 * k + 1)
  have f1 := deformation_neg_sub_eq_sinh δ (2 * k)
  have f2 := deformation_neg_sub_eq_sinh δ (2 * k + 1)
  have g1 : deformation δ (2 * k) - deformation (-δ) (2 * k)
      = -(2 * Real.sinh (δ * Real.log (((2 * k : ℕ) : ℝ) + 1))) := by linarith
  have g2 : deformation δ (2 * k + 1) - deformation (-δ) (2 * k + 1)
      = -(2 * Real.sinh (δ * Real.log (((2 * k + 1 : ℕ) : ℝ) + 1))) := by linarith
  rw [g1] at e1; rw [g2] at e2
  push_cast at e1 e2 ⊢
  linear_combination (1 / 2 : ℂ) * (e1 + e2)

/-- **The exact single-height content of a vanishing at radial deformation `δ`, read on the
undeformed state.**  For `|δ| < ½`: `laneChart3D (½+δ) y = 0` iff the midpoint configuration
`m(y)` is annihilated by both the `cosh(δ·log)`- and the `sinh(δ·log)`-weighted paired sums.
(Uses P1: the partner adds no chart equation.) -/
theorem chart_zero_iff_moments {δ : ℝ} (hδ : |δ| < 1 / 2) (y : ℝ) :
    laneChart3D (1 / 2 + δ) y = 0 ↔ (coshMoment δ y = 0 ∧ sinhMoment δ y = 0) := by
  constructor
  · intro h
    have hp := partner_of_vanishing hδ h
    have := (partner_vanishing_iff_even_odd δ y).mp ⟨h, hp⟩
    rw [evenChart_eq_coshMoment hδ, oddChart_eq_neg_sinhMoment hδ] at this
    exact ⟨this.1, neg_eq_zero.mp this.2⟩
  · rintro ⟨hc, hs⟩
    have : evenChart δ y = 0 ∧ oddChart δ y = 0 := by
      rw [evenChart_eq_coshMoment hδ, oddChart_eq_neg_sinhMoment hδ, hc, hs]; simp
    exact ((partner_vanishing_iff_even_odd δ y).mpr this).1

/-- At `δ = 0` the cosh-moment is the midpoint chart and the sinh-moment vanishes: the midpoint
zero is the `δ = 0` member of the family. -/
theorem coshMoment_zero (y : ℝ) : coshMoment 0 y = laneChart3D (1 / 2) y := by
  unfold coshMoment
  rw [laneChart3D_eq_tsum]
  refine tsum_congr fun k => ?_
  unfold laneSummand
  simp

theorem sinhMoment_zero (y : ℝ) : sinhMoment 0 y = 0 := by
  unfold sinhMoment
  simp

/-- **The forced `E = E_mid` relation, from a single vanishing.**  If the chart vanishes at
`(½+δ, y)` then the midpoint chart at the same height is `−½` times the asymmetry-energy sum of
the midpoint configuration (coefficients `q + q⁻¹ − 2 ≥ 0`, zero iff `δ = 0`). -/
theorem midpoint_chart_of_vanishing {δ : ℝ} (hδ : |δ| < 1 / 2) {y : ℝ}
    (h : laneChart3D (1 / 2 + δ) y = 0) :
    laneChart3D (1 / 2) y = -(1 / 2) * ∑' k, asymmetrySummand δ y k :=
  midpoint_chart_of_partner_vanishing hδ h (partner_of_vanishing hδ h)

end CarrierReadout
