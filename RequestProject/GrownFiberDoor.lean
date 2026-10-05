import RequestProject.GrownFiberConverges
import RequestProject.HurwitzLimit
import RequestProject.RHSourceStatement

/-!
# T2c rebuilt on the growth head: the door (Sam, 2026-09-10)

The frame's objects only: the carrier's grown fiber `finiteFiber Z` with its smooth entry window and head `Z`, and the
carrier's own heads `physicalHead y`.  No strip, no flow on a transform.

* `farBand` — the far side of the readout axis below the Euler edge, `½ < Re s < 1`, in the chart; on the helix this is
  the radial power the balanced carrier does not carry.
* **`HeadClean Z`** — the clause: once the head has climbed past any fixed region on the far side, the grown fiber has
  no event there ("one clean cancellation per carrier height": with the two ends exchanged by J, an event on the far
  side would be a second event at the same height).
* **`rh_of_headClean`** — the door: `HeadClean Z → RiemannHypothesis` for any head sequence `Z n → ∞` (Hurwitz on the
  band through `finiteFiber_tendstoLocallyUniformlyOn`, then the two ends).
* `rh_of_carrierHeadClean` — the door on the carrier's own heads `physicalHead n`.
-/

open Complex Filter Topology Set
open CriticalLinePhasor.CarrierHeadFiniteFiber
open CriticalLinePhasor.BankNoTransient

namespace CriticalLinePhasor.GrownFiber

/-- The far side of the readout axis below the Euler edge: `½ < Re s < 1`. -/
def farBand : Set ℂ := {s : ℂ | 1 / 2 < s.re ∧ s.re < 1}

theorem isOpen_farBand : IsOpen farBand :=
  (isOpen_lt continuous_const Complex.continuous_re).inter (isOpen_lt Complex.continuous_re continuous_const)

theorem convex_farBand : Convex ℝ farBand :=
  (convex_halfSpace_re_gt (1 / 2)).inter (convex_halfSpace_re_lt 1)

theorem farBand_subset_rightHalf : farBand ⊆ {s : ℂ | 0 < s.re} := fun s hs => by
  have := hs.1
  show 0 < s.re
  linarith

theorem ne_one_of_mem_farBand {s : ℂ} (hs : s ∈ farBand) : s ≠ 1 := by
  intro h1
  have := hs.2
  rw [h1] at this
  simp at this

/-- On the far side the conduction factor `1 − 2^{1−s}` does not vanish. -/
theorem conduction_ne_zero {s : ℂ} (hs : s.re < 1) : (1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - s) ≠ 0 := by
  intro h
  have h2 : (2 : ℂ) ^ ((1 : ℂ) - s) = 1 := by linear_combination -h
  have hn := congrArg norm h2
  rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num), norm_one] at hn
  have hre : 0 < ((1 : ℂ) - s).re := by simp only [Complex.sub_re, Complex.one_re]; linarith
  have := Real.one_lt_rpow (by norm_num : (1 : ℝ) < 2) hre
  linarith

/-- The eta readout on the far side is the conduction factor times zeta. -/
theorem etaTailLimit_eq_on_farBand {s : ℂ} (hs : s ∈ farBand) :
    etaTailLimit s = (1 - (2 : ℂ) ^ ((1 : ℂ) - s)) * riemannZeta s :=
  etaTailLimit_eq_etaProduct (by have := hs.1; linarith) (ne_one_of_mem_farBand hs)

/-- **The clause.** Once the head has climbed past any fixed compact region on the far side, the grown fiber has no
event there. -/
def HeadClean (Z : ℕ → ℝ) : Prop :=
  ∀ K : Set ℂ, K ⊆ farBand → IsCompact K → ∀ᶠ n in atTop, ∀ s ∈ K, finiteFiber (Z n) s ≠ 0

/-- Zeta does not vanish identically on the far side: `ζ(¾) ≠ 0` (a zero there would be a nontrivial zero with
imaginary part `0`). -/
theorem riemannZeta_three_quarters_ne_zero : riemannZeta (3 / 4 : ℂ) ≠ 0 := by
  intro h0
  have him := riemannZeta_nontrivial_zero_im_ge_two h0 (by
    intro n hn
    have := congrArg Complex.re hn
    simp at this
    linarith)
  simp at him
  linarith

/-- The eta readout is not identically zero near any point of the far side. -/
theorem etaTailLimit_not_eqOn_zero_ball {ρ : ℂ} (hρ : ρ ∈ farBand) {r : ℝ} (hr : 0 < r)
    (hball : Metric.ball ρ r ⊆ farBand) : ∃ z ∈ Metric.ball ρ r, etaTailLimit z ≠ 0 := by
  by_contra hall
  push Not at hall
  -- ζ vanishes on the ball
  have hζ : ∀ z ∈ Metric.ball ρ r, riemannZeta z = 0 := by
    intro z hz
    have hzb := hball hz
    have h := hall z hz
    rw [etaTailLimit_eq_on_farBand hzb] at h
    exact (mul_eq_zero.mp h).resolve_left (conduction_ne_zero hzb.2)
  -- hence on the whole (convex) band, by the identity theorem
  have hana : AnalyticOnNhd ℂ riemannZeta farBand := by
    apply DifferentiableOn.analyticOnNhd _ isOpen_farBand
    intro z hz
    exact (differentiableAt_riemannZeta (ne_one_of_mem_farBand hz)).differentiableWithinAt
  have hev : riemannZeta =ᶠ[𝓝 ρ] 0 := by
    filter_upwards [Metric.ball_mem_nhds ρ hr] with z hz
    exact hζ z hz
  have hzero := hana.eqOn_zero_of_preconnected_of_eventuallyEq_zero convex_farBand.isPreconnected hρ hev
  have h34 : (3 / 4 : ℂ) ∈ farBand := by
    constructor <;> norm_num
  exact riemannZeta_three_quarters_ne_zero (hzero h34)

/-- The mirror of a zero is a zero (the two ends exchanged by J; the functional equation in the chart). -/
theorem one_sub_mem_zeros {ρ : ℂ} (hρ : ρ ∈ ZD.NontrivialZeros) : 1 - ρ ∈ ZD.NontrivialZeros := by
  obtain ⟨h0, h1, hz⟩ := hρ
  refine ⟨by simp; linarith, by simp; linarith, ?_⟩
  have hn : ∀ n : ℕ, ρ ≠ -n := by
    intro n h
    have := congrArg Complex.re h
    simp at this
    linarith
  have h1' : ρ ≠ 1 := by
    intro h; rw [h] at h1; simp at h1
  rw [riemannZeta_one_sub hn h1', hz]
  simp

/-- **The door: RH from the clause, for any head sequence tending to infinity.** -/
theorem rh_of_headClean (Z : ℕ → ℝ) (hZ : Tendsto Z atTop atTop) (h : HeadClean Z) : RiemannHypothesis := by
  apply DoubleCoshProgram.RiemannHypothesis_of_no_offline
  -- no zero on the far side
  have key : ∀ ρ ∈ ZD.NontrivialZeros, 1 / 2 < ρ.re → False := by
    intro ρ hρ hre
    have hband : ρ ∈ farBand := ⟨hre, hρ.2.1⟩
    have hη : etaTailLimit ρ = 0 := by
      rw [etaTailLimit_eq_on_farBand hband, hρ.2.2, mul_zero]
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_farBand ρ hband
    have hKsub : Metric.closedBall ρ (r / 2) ⊆ farBand :=
      (Metric.closedBall_subset_ball (by linarith)).trans hball
    obtain ⟨n₀, hn₀⟩ := (h _ hKsub (isCompact_closedBall _ _)).exists_forall_of_atTop
    -- the tail of the head sequence, on the open ball
    set F : ℕ → ℂ → ℂ := fun k => finiteFiber (Z (k + n₀)) with hF
    have hconv : TendstoLocallyUniformlyOn F etaTailLimit atTop (Metric.ball ρ (r / 2)) := by
      have h1 := (finiteFiber_tendstoLocallyUniformlyOn Z hZ).mono
        (Metric.ball_subset_closedBall.trans (hKsub.trans farBand_subset_rightHalf))
      intro u hu x hx
      obtain ⟨t, ht, hev⟩ := h1 u hu x hx
      exact ⟨t, ht, (tendsto_add_atTop_nat n₀).eventually hev⟩
    have hFne : ∀ k, ∀ z ∈ Metric.ball ρ (r / 2), F k z ≠ 0 := fun k z hz =>
      hn₀ (k + n₀) (by omega) z (Metric.ball_subset_closedBall hz)
    have hne := CriticalLinePhasor.Hurwitz.ne_zero_of_tendstoLocallyUniformlyOn Metric.isOpen_ball
      (convex_ball ρ (r / 2)).isPreconnected (fun k => (finiteFiber_entire _).differentiableOn) hFne hconv
      (etaTailLimit_not_eqOn_zero_ball hband (by linarith) (Metric.ball_subset_closedBall.trans hKsub))
      ρ (Metric.mem_ball_self (by linarith))
    exact hne hη
  intro ρ hρ
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hm := one_sub_mem_zeros hρ
    apply key (1 - ρ) hm
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  · exact key ρ hρ hgt

/-! ### On the carrier's own heads -/

/-- The carrier's heads at the integer ordinates, `W(n) = physicalHead n`. -/
noncomputable def carrierHeads (n : ℕ) : ℝ := physicalHead n

theorem carrierHeads_tendsto : Tendsto carrierHeads atTop atTop :=
  physicalHead_tendsto.comp tendsto_natCast_atTop_atTop

/-- **RH from the clause on the carrier's own heads.** -/
theorem rh_of_carrierHeadClean (h : HeadClean carrierHeads) : RiemannHypothesis :=
  rh_of_headClean carrierHeads carrierHeads_tendsto h

end CriticalLinePhasor.GrownFiber

#print axioms CriticalLinePhasor.GrownFiber.rh_of_headClean
#print axioms CriticalLinePhasor.GrownFiber.rh_of_carrierHeadClean
