import RequestProject.CarrierBank
import RequestProject.CarrierRegistration
import RequestProject.CarrierParityQuantization
import RequestProject.Phasor3D

/-!
# The warped fiber on the scaled carrier IS the one-dimensional function

The paper defines the carrier fiber `F_Δ(s) = Δ^{−s}(1 − 2^{1−s})ζ(s)`
(`CarrierParity.carrierFiber`) and describes it as "the sum over the sites `x_n = Δ n` of the
phasors `x_n^{−s}`, the odd and even sites entering with opposite sign".  In the sources that
description was not a theorem: `carrierFiber` is *defined* by the closed form.  This file
proves the description, unconditionally, on the whole channel where the ordered sum converges,
and then proves that the one-dimensional function has no content beyond it.

* `bankΔ Δ s` is the bank on the carrier of scale `Δ` — the phasor `x_{n+1}^{−s}` at the site
  `x_{n+1} = Δ(n+1)` — and `bankΔ_eq_exp` says it is the warp `e^{−sH_Δ}𝟙`: the phasor is
  `exp(−s · λ_n(H_Δ))`, `λ_n(H_Δ) = log(Δ(n+1))` the eigenvalue of the scaled generator.
* `bankΔ_eq_scale` : the carrier scale is a gauge on the bank, `bankΔ Δ s = Δ^{−s} · bank s`.
* **`fiber_eq_function`** : for `Δ > 0`, `Re s > 0`, `s ≠ 1`,
  `laneChart (bankΔ Δ s) = carrierFiber Δ s` — the lane-balanced chart of the warped bank on
  the scaled carrier IS `Δ^{−s}(1 − 2^{1−s})ζ(s)`, the analytic function, not a truncation.
* `zeta_zero_iff_bankΔ_mem_ker` : in the strip, `ζ(s) = 0 ⟺ bankΔ Δ s ∈ ker(lane chart)`, at
  every carrier scale.
* **`fiber3D_eq_function`** : the same identity read on the *three-dimensional* phasors of
  `Phasor3D`: the planar projections of `phasor3D χ₂ σ y n` (χ₂ the conductor-2 lane
  character), summed in the order they enter, in pairs, and scaled by `Δ^{−s}`, equal
  `carrierFiber Δ (σ + iy)`.  (`plane_phasor3D_eq`: the planar projection of the 3-D phasor is
  the lane sign times the bank's phasor.)
* **`function_determined_by_fiber`** : any entire function that agrees with the fiber's chart
  on the channel `Re s > 0` equals `(1 − 2^{1−s})ζ(s)` at every `s ≠ 1` — the identity theorem
  on the connected open set `ℂ ∖ {1}`.  So off the channel, where the ordered sum does not
  converge, the one-dimensional function is still *determined* by the fiber, and by nothing
  else.

Every statement is unconditional.  The honest boundary: the chart converges exactly on
`Re s > 0` (that is the whole point of the lane split, §4 of the paper); to the left of it
"the same thing" means "uniquely determined by", which is the last theorem.
-/

open scoped BigOperators
open CriticalLinePhasor

noncomputable section

namespace CarrierReadout

/-! ### 1. The warped bank on the scaled carrier -/

/-- The bank at carrier scale `Δ` and height `s`: the phasor `x_{n+1}^{−s}` at the site
`x_{n+1} = Δ(n+1)`. -/
def bankΔ (Δ : ℝ) (s : ℂ) : ℕ → ℂ := fun n => ((Δ * ((n : ℝ) + 1) : ℝ) : ℂ) ^ (-s)

/-- **The warp on the scaled carrier**: `bankΔ Δ s = e^{−sH_Δ}𝟙` — the phasor at site `n+1` is
`exp(−s · λ_n(H_Δ))` with `λ_n(H_Δ) = carrierLogWeight Δ n = log(Δ(n+1))`. -/
theorem bankΔ_eq_exp (Δ : ℝ) (hΔ : 0 < Δ) (s : ℂ) (n : ℕ) :
    bankΔ Δ s n = Complex.exp (-s * (carrierLogWeight Δ n : ℂ)) := by
  have hpos : (0 : ℝ) < Δ * ((n : ℝ) + 1) := by positivity
  have hne : ((Δ * ((n : ℝ) + 1) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  unfold bankΔ carrierLogWeight
  rw [Complex.cpow_def_of_ne_zero hne, ← Complex.ofReal_log hpos.le]
  congr 1
  ring

/-- **The carrier scale is a gauge on the bank**: `bankΔ Δ s = Δ^{−s} · bank s`. -/
theorem bankΔ_eq_scale (Δ : ℝ) (hΔ : 0 < Δ) (s : ℂ) (n : ℕ) :
    bankΔ Δ s n = (Δ : ℂ) ^ (-s) * bank s n := by
  unfold bankΔ bank
  rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hΔ.le (by positivity)]
  push_cast
  ring

/-- The lane chart of the scaled bank is `Δ^{−s}` times that of the unit bank. -/
theorem laneChart_bankΔ (Δ : ℝ) (hΔ : 0 < Δ) (s : ℂ) :
    laneChart (bankΔ Δ s) = (Δ : ℂ) ^ (-s) * laneChart (bank s) := by
  unfold laneChart
  rw [← tsum_mul_left]
  refine tsum_congr fun k => ?_
  rw [bankΔ_eq_scale Δ hΔ, bankΔ_eq_scale Δ hΔ]
  ring

/-! ### 2. The fiber is the function -/

/-- **THE FIBER IS THE FUNCTION.**  On the whole channel `Re s > 0`, `s ≠ 1`, the lane-balanced
chart of the warped bank on the carrier of scale `Δ` equals the carrier fiber
`F_Δ(s) = Δ^{−s}(1 − 2^{1−s})ζ(s)`: the one-dimensional analytic function, not a truncation of
it.  Unconditional. -/
theorem fiber_eq_function (Δ : ℝ) (hΔ : 0 < Δ) {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    laneChart (bankΔ Δ s) = CarrierParity.carrierFiber Δ s := by
  rw [laneChart_bankΔ Δ hΔ, laneChart_bank, DVP.etaLim_eq_zeta hs hs1]
  rfl

/-- **The events are the same at every carrier scale**: in the strip, `ζ(s) = 0` iff the scaled
bank lies in the kernel of the lane chart. -/
theorem zeta_zero_iff_bankΔ_mem_ker (Δ : ℝ) (hΔ : 0 < Δ) {s : ℂ} (hs0 : 0 < s.re)
    (hs1 : s.re < 1) :
    riemannZeta s = 0 ↔ laneChart (bankΔ Δ s) = 0 := by
  have hne : (Δ : ℂ) ^ (-s) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]
    rintro ⟨h, -⟩
    exact hΔ.ne' (by exact_mod_cast h)
  rw [laneChart_bankΔ Δ hΔ, mul_eq_zero, zeta_zero_iff_bank_mem_ker hs0 hs1]
  constructor
  · intro h; exact Or.inr h
  · rintro (h | h)
    · exact absurd h hne
    · exact h

/-! ### 3. The same identity on the three-dimensional phasors -/

/-- The conductor-2 lane character: `+1` on odd sites, `−1` on even sites, `0` at the origin
(there is no site at the origin). -/
def chi2 : ℕ → ℂ := fun n => if n = 0 then 0 else if n % 2 = 1 then 1 else -1

/-- The bank's phasor at site `n+1`, at height `s = σ + iy`, is the magnitude `(n+1)^{−σ}` times
the Mellin spin `exp(−i y log(n+1))`: modulus and phase, as §4 of the paper reads them. -/
theorem bank_eq_rpow_mul_spin (σ y : ℝ) (n : ℕ) :
    bank ((σ : ℂ) + y * Complex.I) n
      = ((((n : ℝ) + 1) ^ (-σ) : ℝ) : ℂ) * LFunctionPhasor.mellinSpin y (n + 1) := by
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hne : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast hpos.ne'
  have hcast : ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
  unfold bank LFunctionPhasor.mellinSpin
  rw [Complex.cpow_def_of_ne_zero hne, hcast, ← Complex.ofReal_log hpos.le,
    Real.rpow_def_of_pos hpos, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- **The planar projection of the 3-D phasor is the lane sign times the bank's phasor.** -/
theorem plane_phasor3D_eq (σ y : ℝ) (n : ℕ) :
    Phasor3D.plane (Phasor3D.phasor3D chi2 σ y (n + 1))
      = chi2 (n + 1) * bank ((σ : ℂ) + y * Complex.I) n := by
  rw [bank_eq_rpow_mul_spin]
  unfold Phasor3D.plane Phasor3D.phasor3D LFunctionPhasor.phasorTerm
  push_cast
  ring

/-- The three-dimensional fiber's chart: the planar projections of the 3-D phasors, summed in
the order the sites enter, in pairs (odd site plus even site). -/
def laneChart3D (σ y : ℝ) : ℂ :=
  ∑' k : ℕ, (Phasor3D.plane (Phasor3D.phasor3D chi2 σ y (2 * k + 1))
            + Phasor3D.plane (Phasor3D.phasor3D chi2 σ y (2 * k + 2)))

theorem laneChart3D_eq (σ y : ℝ) :
    laneChart3D σ y = laneChart (bank ((σ : ℂ) + y * Complex.I)) := by
  unfold laneChart3D laneChart
  refine tsum_congr fun k => ?_
  have h2 : 2 * k + 2 = (2 * k + 1) + 1 := by ring
  rw [h2, plane_phasor3D_eq, plane_phasor3D_eq]
  have c1 : chi2 (2 * k + 1) = 1 := by
    simp [chi2, show (2 * k + 1) % 2 = 1 by omega]
  have c2 : chi2 (2 * k + 1 + 1) = -1 := by
    simp [chi2, show (2 * k + 1 + 1) % 2 = 0 by omega]
  rw [c1, c2]
  ring

/-- **THE WARPED 3-D FIBER ON THE SCALED CARRIER IS THE ONE-DIMENSIONAL FUNCTION.**  For
`Δ > 0`, `σ > 0` and `σ + iy ≠ 1`, the planar projections of the three-dimensional phasors
`phasor3D χ₂ σ y n`, summed in the order they enter and scaled by `Δ^{−s}`, equal the carrier
fiber `F_Δ(σ + iy) = Δ^{−s}(1 − 2^{1−s})ζ(s)`.  Unconditional. -/
theorem fiber3D_eq_function (Δ : ℝ) (hΔ : 0 < Δ) (σ y : ℝ) (hσ : 0 < σ)
    (hs1 : (σ : ℂ) + y * Complex.I ≠ 1) :
    (Δ : ℂ) ^ (-((σ : ℂ) + y * Complex.I)) * laneChart3D σ y
      = CarrierParity.carrierFiber Δ ((σ : ℂ) + y * Complex.I) := by
  have hre : 0 < ((σ : ℂ) + y * Complex.I).re := by simpa using hσ
  rw [laneChart3D_eq, ← laneChart_bankΔ Δ hΔ, fiber_eq_function Δ hΔ hre hs1]

/-! ### 4. The function has no content beyond the fiber -/

/-- **The one-dimensional function is determined by the fiber's chart.**  Any entire function
that agrees with the lane chart of the bank on the channel `Re s > 0` (off `s = 1`) equals
`(1 − 2^{1−s})ζ(s)` at every `s ≠ 1`: the identity theorem on the connected open set
`ℂ ∖ {1}`. -/
theorem function_determined_by_fiber {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (hagree : ∀ s : ℂ, 0 < s.re → s ≠ 1 → g s = laneChart (bank s)) :
    ∀ s : ℂ, s ≠ 1 → g s = (1 - (2 : ℂ) ^ ((1 : ℂ) - s)) * riemannZeta s := by
  set h : ℂ → ℂ := fun s => (1 - (2 : ℂ) ^ ((1 : ℂ) - s)) * riemannZeta s with hh
  have hU : IsOpen ({1}ᶜ : Set ℂ) := isOpen_compl_singleton
  have hconn : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank (by rw [Complex.rank_real_complex]; norm_num)
      (1 : ℂ)).isPreconnected
  have hgA : AnalyticOnNhd ℂ g {1}ᶜ := hg.differentiableOn.analyticOnNhd hU
  have hhD : DifferentiableOn ℂ h {1}ᶜ := by
    intro s hs
    have hs1 : s ≠ 1 := hs
    refine DifferentiableAt.differentiableWithinAt ?_
    apply DifferentiableAt.mul
    · apply DifferentiableAt.const_sub
      apply DifferentiableAt.const_cpow (differentiableAt_const _ |>.sub differentiableAt_id)
      exact Or.inl (by norm_num)
    · exact differentiableAt_riemannZeta hs1
  have hhA : AnalyticOnNhd ℂ h {1}ᶜ := hhD.analyticOnNhd hU
  have hmem : ({s : ℂ | 0 < s.re} ∩ {1}ᶜ) ∈ nhds (2 : ℂ) := by
    apply IsOpen.mem_nhds
    · exact (isOpen_lt continuous_const Complex.continuous_re).inter hU
    · constructor
      · show (0 : ℝ) < (2 : ℂ).re; norm_num
      · show (2 : ℂ) ≠ 1; norm_num
  have hfg : g =ᶠ[nhds (2 : ℂ)] h := by
    filter_upwards [hmem] with s hs
    obtain ⟨hre, hs1⟩ := hs
    have hs1' : s ≠ 1 := hs1
    rw [hagree s hre hs1', laneChart_bank, DVP.etaLim_eq_zeta hre hs1']
  have h2 : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) := by show (2 : ℂ) ≠ 1; norm_num
  have heq := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hgA hhA hconn h2 hfg
  intro s hs
  exact heq hs

end CarrierReadout
