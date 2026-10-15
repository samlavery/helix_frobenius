import RequestProject.XiRadialAmplitude
import RequestProject.ZeroCountJensen
import RequestProject.RiemannHypothesisBridge
import RequestProject.DVPBridgeGeneral
import RequestProject.HelixSourceEndSwap

/-!
# The tilt-mass door, in the geometry's words (ledger 1326; window removed 1328)

Geometry first (Sam, 2026-10-13). The chart's abscissa `σ` is the TILT of the projection plane into the height
direction (1325, frame B): site `n` is weighted by `e^{−δ h_n} = n^{−δ}`, `δ = σ − ½`. The mass of the native state
read through the tilt `σ` at height `t` is `tiltMass t σ = |ξ(σ + it)|²` (ξ, not ζ: the two-ended completed
resultant, real on the axis by the reflection about `h = 0`).

Sam's sentence "a drifted evaluation does not cancel" is here the statement that the mass does not DECREASE as the
tilt grows. Three compiled doors, each weaker than the strict native seat (`riemannHypothesis_of_native_seat`):

* `riemannHypothesis_of_tiltMass_nondecreasing` — the NON-STRICT sign `0 ≤ Re(ξ·conj ξ′)` on the open right
  half-strip `½ < Re s < 1` suffices. No verified window is used (Sam, 2026-10-13: "don't use verified windows").
  Mechanism: a zero at tilt `β` would pin the mass at `0` on the whole segment `[½, β]` of its height, and an entire
  function vanishing on a segment vanishes identically (`ξ(0) = ½`).
* `riemannHypothesis_of_logDeriv_re_nonneg` — the same, as the sign of the drift derivative of the LOG-mass,
  `0 ≤ Re(ξ′/ξ)`, needed only where `ξ ≠ 0`.
* `riemannHypothesis_of_prime_coherence_le_winding` — the 1323 form: wherever `ζ(s) ≠ 0` in that region, the prime
  clocks' in-phase coherence `C(s) = −Re(ζ′/ζ)` does not exceed the carrier's winding density
  `W(s) = Re(1/s + 1/(s−1) + Γℝ′/Γℝ)`. The split is `bridge_pillar_general`.

Also `oneVanishing_iff_rh`: Sam's proposition `OneVanishingPerHeight3D` (1314) is exactly `RiemannHypothesis`, both
directions compiled, so the doors above are doors to it as well (`oneVanishing_of_tiltMass`).

All doors are EQUIV (the leaf is the seat sign condition, 505–512); the gain is the form: the hypothesis is stated on
the native mass, non-strictly, on the open right half-strip, with the DC (`W`) isolated.
No `sorry`, no `axiom`.
-/

open Complex ComplexConjugate Filter Topology Set

noncomputable section

namespace CriticalLinePhasor.HelixTiltMass

open CriticalLinePhasor.XiStructure CriticalLinePhasor.HelixZetaSource CriticalLinePhasor.HelixSourceEndSwap

/-- The mass of the native state at height `t`, read through the tilt `σ`. -/
def tiltMass (t σ : ℝ) : ℝ := Complex.normSq (ZD.riemannXi (↑σ + ↑t * Complex.I))

/-- The cross term `Re(ξ·conj ξ′)`: half the drift derivative of the tilt mass. -/
def cross (s : ℂ) : ℝ := (ZD.riemannXi s * conj (deriv ZD.riemannXi s)).re

/-- The region where the sign is asked: the open right half-strip. -/
def Region (s : ℂ) : Prop := 1 / 2 < s.re ∧ s.re < 1

theorem tiltMass_hasDerivAt (t σ : ℝ) :
    HasDerivAt (tiltMass t) (2 * cross (↑σ + ↑t * Complex.I)) σ :=
  radial_amplitude_hasDerivAt t σ

theorem re_path (t σ : ℝ) : ((σ : ℂ) + ↑t * Complex.I).re = σ := by simp

theorem im_path (t σ : ℝ) : ((σ : ℂ) + ↑t * Complex.I).im = t := by simp

/-- **The mass does not decrease under tilt** on `[½, 1]` at height `t`, given the non-strict sign on `(½, 1)`. -/
theorem tiltMass_monotoneOn (t : ℝ)
    (h : ∀ σ : ℝ, 1 / 2 < σ → σ < 1 → 0 ≤ cross (↑σ + ↑t * Complex.I)) :
    MonotoneOn (tiltMass t) (Icc (1 / 2 : ℝ) 1) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
  · exact fun σ _ => (tiltMass_hasDerivAt t σ).continuousAt.continuousWithinAt
  · exact fun σ _ => (tiltMass_hasDerivAt t σ).differentiableAt.differentiableWithinAt
  · intro σ hσ
    rw [interior_Icc, mem_Ioo] at hσ
    rw [(tiltMass_hasDerivAt t σ).deriv]
    exact mul_nonneg (by norm_num) (h σ hσ.1 hσ.2)

/-- **No cancellation at a positive tilt in the region.** If the cross term is nonnegative on the region, `ξ` has no
zero there: the mass would vanish on the segment `[½, β]` at the zero's height, and `ξ` is entire with `ξ(0) = ½`. -/
theorem xi_ne_zero_of_cross_nonneg (h : ∀ s : ℂ, Region s → 0 ≤ cross s)
    {s : ℂ} (hs : Region s) : ZD.riemannXi s ≠ 0 := by
  intro h0
  obtain ⟨hs1, hs2⟩ := hs
  set t := s.im with ht
  set β := s.re with hβ
  have hs_eq : s = (β : ℂ) + ↑t * Complex.I := by
    apply Complex.ext <;> simp [hβ, ht]
  have hmono := tiltMass_monotoneOn t
    (fun σ hσ1 hσ2 => h _ ⟨by rw [re_path]; exact hσ1, by rw [re_path]; exact hσ2⟩)
  -- the mass vanishes on the whole segment `[½, β]`
  have hzero : ∀ σ : ℝ, 1 / 2 ≤ σ → σ ≤ β → ZD.riemannXi (↑σ + ↑t * Complex.I) = 0 := by
    intro σ h1 h2
    have hle := hmono ⟨h1, by linarith⟩ ⟨by linarith, hs2.le⟩ h2
    have hβ0 : tiltMass t β = 0 := by
      simp only [tiltMass]; rw [← hs_eq, h0, Complex.normSq_zero]
    have : tiltMass t σ = 0 := le_antisymm (hβ0 ▸ hle) (Complex.normSq_nonneg _)
    exact Complex.normSq_eq_zero.mp this
  -- the path `σ ↦ σ + it`, `σ → β⁻`, enters every punctured neighbourhood of `s` through zeros of `ξ`
  have hpath : Tendsto (fun σ : ℝ => (σ : ℂ) + ↑t * Complex.I) (𝓝[<] β) (𝓝[≠] s) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have hc : Continuous (fun σ : ℝ => (σ : ℂ) + ↑t * Complex.I) :=
        Complex.continuous_ofReal.add continuous_const
      have : Tendsto (fun σ : ℝ => (σ : ℂ) + ↑t * Complex.I) (𝓝[<] β) (𝓝 ((β : ℂ) + ↑t * Complex.I)) :=
        (hc.tendsto β).mono_left nhdsWithin_le_nhds
      rwa [← hs_eq] at this
    · filter_upwards [self_mem_nhdsWithin] with σ hσ
      rw [mem_Iio] at hσ
      intro heq
      have := congrArg Complex.re heq
      rw [re_path] at this
      exact absurd this (ne_of_lt hσ)
  have hfreq : ∃ᶠ z in 𝓝[≠] s, ZD.riemannXi z = 0 := by
    apply hpath.frequently
    apply Eventually.frequently
    filter_upwards [Ioo_mem_nhdsLT hs1] with σ hσ
    exact hzero σ hσ.1.le hσ.2.le
  have hEq : Set.EqOn ZD.riemannXi 0 Set.univ :=
    (ZD.ZeroCount.riemannXi_analyticOnNhd_univ).eqOn_zero_of_preconnected_of_frequently_eq_zero
      (isPreconnected_univ : IsPreconnected (Set.univ : Set ℂ)) (Set.mem_univ s) hfreq
  have h00 := hEq (Set.mem_univ 0)
  simp only [Pi.zero_apply] at h00
  exact ZD.ZeroCount.riemannXi_zero_ne_zero h00

/-- Every nontrivial zero lies on the axis: by the tilt-mass sign on the right and the reflection `ξ(1 − s) = ξ(s)`
on the left. -/
theorem zeros_on_line_of_cross_nonneg (h : ∀ s : ℂ, Region s → 0 ≤ cross s) :
    ∀ ρ ∈ ZD.NontrivialZeros, ρ.re = 1 / 2 := by
  intro ρ hρ
  have hξ := ZD.ZeroCount.riemannXi_zero_of_mem_NontrivialZeros ρ hρ
  obtain ⟨hre0, hre1, _⟩ := hρ
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hreg : Region (1 - ρ) := by
      refine ⟨?_, ?_⟩
      · rw [Complex.sub_re, Complex.one_re]; linarith
      · rw [Complex.sub_re, Complex.one_re]; linarith
    exact xi_ne_zero_of_cross_nonneg h hreg (by rw [ZD.ZeroCount.riemannXi_one_sub]; exact hξ)
  · exact xi_ne_zero_of_cross_nonneg h ⟨hgt, hre1⟩ hξ

/-- **Door 1 — the tilt mass does not decrease** on the open right half-strip. -/
theorem riemannHypothesis_of_tiltMass_nondecreasing (h : ∀ s : ℂ, Region s → 0 ≤ cross s) :
    RiemannHypothesis :=
  RHBridge.no_offline_zeros_implies_rh (zeros_on_line_of_cross_nonneg h)

/-- The strict native seat implies the hypothesis of Door 1. -/
theorem cross_nonneg_of_strict_seat
    (hseat : ∀ s : ℂ, 1 / 2 < s.re → 0 < (ZD.riemannXi s * conj (deriv ZD.riemannXi s)).re) :
    ∀ s : ℂ, Region s → 0 ≤ cross s :=
  fun s hs => (hseat s hs.1).le

/-! ## Door 2 — the drift derivative of the log-mass -/

/-- `Re(ξ·conj ξ′) = |ξ|²·Re(ξ′/ξ)`: the cross term is the mass times the drift derivative of the log-mass. -/
theorem cross_eq_normSq_mul_re_logDeriv (s : ℂ) :
    cross s = Complex.normSq (ZD.riemannXi s) * (deriv ZD.riemannXi s / ZD.riemannXi s).re := by
  unfold cross
  by_cases h0 : ZD.riemannXi s = 0
  · simp [h0]
  rw [Complex.div_re, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  have hn : Complex.normSq (ZD.riemannXi s) ≠ 0 := fun h => h0 (Complex.normSq_eq_zero.mp h)
  field_simp
  ring

/-- **Door 2.** The sign of the drift derivative of the log-mass, needed only where the mass is positive. -/
theorem riemannHypothesis_of_logDeriv_re_nonneg
    (h : ∀ s : ℂ, Region s → ZD.riemannXi s ≠ 0 → 0 ≤ (deriv ZD.riemannXi s / ZD.riemannXi s).re) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_tiltMass_nondecreasing
  intro s hs
  rw [cross_eq_normSq_mul_re_logDeriv]
  by_cases h0 : ZD.riemannXi s = 0
  · simp [h0]
  · exact mul_nonneg (Complex.normSq_nonneg _) (h s hs h0)

/-! ## Door 3 — prime coherence ≤ winding density (1323) -/

/-- The carrier's winding density at `s`: the DC of the drift derivative of the log-mass. -/
def windingDensity (s : ℂ) : ℝ := (1 / s + 1 / (s - 1) + logDeriv Complex.Gammaℝ s).re

/-- The prime clocks' in-phase coherence at `s`: `−Re(ζ′/ζ)`. -/
def primeCoherence (s : ℂ) : ℝ := -(deriv riemannZeta s / riemannZeta s).re

/-- **The split** `Re(ξ′/ξ) = W − C` wherever `ζ(s) ≠ 0`, `s ≠ 0, 1`, `Re s > 0` (`bridge_pillar_general`). -/
theorem re_logDeriv_xi_eq_winding_sub_coherence {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hre : 0 < s.re)
    (hζ : riemannZeta s ≠ 0) :
    (deriv ZD.riemannXi s / ZD.riemannXi s).re = windingDensity s - primeCoherence s := by
  have hb := CriticalLinePhasor.DVP.bridge_pillar_general s hs0 hs1 hre hζ
  have hxi : (VMEFStandalone.riemannXi : ℂ → ℂ) = ZD.riemannXi := rfl
  rw [hxi] at hb
  unfold windingDensity primeCoherence
  have : deriv ZD.riemannXi s / ZD.riemannXi s =
      deriv riemannZeta s / riemannZeta s + (1 / s + 1 / (s - 1) + logDeriv Complex.Gammaℝ s) := by
    rw [hb]; ring
  rw [this, Complex.add_re]; ring

/-- In the strip, a point at which `ξ ≠ 0` has `ζ ≠ 0`. -/
theorem zeta_ne_zero_of_xi_ne_zero {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) (hξ : ZD.riemannXi s ≠ 0) :
    riemannZeta s ≠ 0 :=
  fun hζ => hξ (ZD.riemannXi_eq_zero_of_mem_NontrivialZeros s ⟨hs0, hs1, hζ⟩)

/-- **Door 3 (1323's sentence).** Wherever the readout is regular in the region, the prime clocks' coherence does not
exceed the carrier's winding density. -/
theorem riemannHypothesis_of_prime_coherence_le_winding
    (h : ∀ s : ℂ, Region s → riemannZeta s ≠ 0 → primeCoherence s ≤ windingDensity s) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_logDeriv_re_nonneg
  intro s hs hξ
  have hζ := zeta_ne_zero_of_xi_ne_zero (by linarith [hs.1]) hs.2 hξ
  have hs0 : s ≠ 0 := fun h0 => by have := hs.1; rw [h0] at this; simp at this; linarith
  have hs1 : s ≠ 1 := fun h1 => by have := hs.2; rw [h1] at this; simp at this
  rw [re_logDeriv_xi_eq_winding_sub_coherence hs0 hs1 (by linarith [hs.1]) hζ]
  exact sub_nonneg.mpr (h s hs hζ)

/-! ## Sam's proposition is exactly RH -/

/-- `RiemannHypothesis → OneVanishingPerHeight3D`: under RH every cancelling abscissa at a height is `½`. -/
theorem oneVanishing_of_rh (hRH : RiemannHypothesis) : CarrierReadout.OneVanishingPerHeight3D := by
  rw [oneVanishing_iff_source]
  intro y σ₁ σ₂ h1 h2 h3 h4 c1 c2
  have key : ∀ σ : ℝ, 0 < σ → σ < 1 →
      (sourceConfig (((σ : ℂ) + y * Complex.I) / 2 - 1 / 4) (Real.exp y) 0).Cancels → σ = 1 / 2 := by
    intro σ hσ0 hσ1 hc
    have hre : ((((σ : ℂ) + y * Complex.I) / 2 - 1 / 4)).re = σ / 2 - 1 / 4 := by simp
    have hv : |((((σ : ℂ) + y * Complex.I) / 2 - 1 / 4)).re| < 1 / 4 := by
      rw [hre, abs_lt]; constructor <;> linarith
    have hζ := (sourceConfig_cancels_iff hv (Real.exp y) 0).mp hc
    have hs : (1 / 2 : ℂ) + 2 * ((((σ : ℂ) + y * Complex.I) / 2 - 1 / 4)) = (σ : ℂ) + y * Complex.I := by
      ring
    rw [hs] at hζ
    have hnt : ¬∃ n : ℕ, ((σ : ℂ) + y * Complex.I) = -2 * (n + 1) := by
      rintro ⟨n, hn⟩
      have := congrArg Complex.re hn
      simp at this
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have hne1 : ((σ : ℂ) + y * Complex.I) ≠ 1 := by
      intro h1'
      have := congrArg Complex.re h1'
      simp at this
      linarith
    have hre' := hRH _ hζ hnt hne1
    simpa using hre'
  rw [key σ₁ h1 h2 c1, key σ₂ h3 h4 c2]

/-- **Sam's proposition (1314) is exactly RH**, both directions compiled. -/
theorem oneVanishing_iff_rh : CarrierReadout.OneVanishingPerHeight3D ↔ RiemannHypothesis :=
  ⟨OneAssumptionRH.riemannHypothesis_of_oneAssumption, oneVanishing_of_rh⟩

/-- The tilt-mass door, landing on Sam's proposition. -/
theorem oneVanishing_of_tiltMass (h : ∀ s : ℂ, Region s → 0 ≤ cross s) :
    CarrierReadout.OneVanishingPerHeight3D :=
  oneVanishing_of_rh (riemannHypothesis_of_tiltMass_nondecreasing h)

end CriticalLinePhasor.HelixTiltMass

end

#print axioms CriticalLinePhasor.HelixTiltMass.riemannHypothesis_of_tiltMass_nondecreasing
#print axioms CriticalLinePhasor.HelixTiltMass.riemannHypothesis_of_logDeriv_re_nonneg
#print axioms CriticalLinePhasor.HelixTiltMass.riemannHypothesis_of_prime_coherence_le_winding
#print axioms CriticalLinePhasor.HelixTiltMass.re_logDeriv_xi_eq_winding_sub_coherence
#print axioms CriticalLinePhasor.HelixTiltMass.oneVanishing_iff_rh
#print axioms CriticalLinePhasor.HelixTiltMass.oneVanishing_of_tiltMass
