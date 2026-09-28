import RequestProject.ZetaScrewFourier
import RequestProject.LFunctionPhasor
import RequestProject.GrownFiberConverges

/-!
# Native nontriviality of the limit object (R64)

`F = BankNoTransient.etaTailLimit` is the unique native object of Theorem A. This module certifies from
native constructors:

* `etaTailLimit_eq_etaLim`. `F = etaLim` on `Re s > 0`: the abrupt partial sums of `F` are the ordered partial sums of
  `etaLim`, so the two limits coincide. The proof is verbatim from `Campaign.R23B2`
  (`tmp/campaign_r23_build_banks.lean`).
* `etaTailLimit_half_ne_zero`. `F(½) ≠ 0`, composing the above with `HilbertPolya.etaLim_half_ne_zero` (every paired
  term at `½` is a positive real).
* `etaTailLimit_analyticOnNhd`, `etaTailLimit_not_eventually_zero`. `F` is analytic on `Re s > 0`, and there is no point
  near which it vanishes identically.
-/

open Complex Filter Topology

noncomputable section

namespace CriticalLinePhasor.NativeNontriviality

open CriticalLinePhasor.BankNoTransient CriticalLinePhasor.CarrierHeadFiniteFiber

/-- `F` is the ordered paired limit on `Re s > 0`: both are limits of one sequence of partial sums. -/
theorem etaTailLimit_eq_etaLim {s : ℂ} (hs : 0 < s.re) : etaTailLimit s = DVP.etaLim s := by
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp at hs
  have h1 := LFunctionPhasor.eta_partialSum_tendsto_tail hs
  have h2 := DVP.etaPartial_tendsto hs
  have h3 : Tendsto (fun N : ℕ => DVP.etaPartial s N) atTop (𝓝 (etaTailLimit s)) := by
    refine (h1.comp (tendsto_add_atTop_nat 1)).congr fun N => ?_
    show GrownFiber.hardPartial (N + 1) s = DVP.etaPartial s N
    rw [← GrownFiber.partialReadout_eq_hardPartial N hs0]
    unfold GrownFiber.partialReadout DVP.etaPartial DVP.etaTerm
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.cpow_neg, div_eq_mul_inv]
  exact tendsto_nhds_unique h3 h2

/-- **Native nontriviality.** `F(½) ≠ 0`. -/
theorem etaTailLimit_half_ne_zero : etaTailLimit (1 / 2 : ℂ) ≠ 0 := by
  rw [etaTailLimit_eq_etaLim (by norm_num)]
  exact HilbertPolya.etaLim_half_ne_zero

theorem etaTailLimit_differentiableOn : DifferentiableOn ℂ etaTailLimit {s : ℂ | 0 < s.re} :=
  (GrownFiber.finiteFiber_tendstoLocallyUniformlyOn (fun n : ℕ => (n : ℝ)) tendsto_natCast_atTop_atTop).differentiableOn
    (Eventually.of_forall fun _ => (finiteFiber_entire _).differentiableOn) GrownFiber.isOpen_rightHalf

theorem etaTailLimit_analyticOnNhd : AnalyticOnNhd ℂ etaTailLimit {s : ℂ | 0 < s.re} :=
  etaTailLimit_differentiableOn.analyticOnNhd GrownFiber.isOpen_rightHalf

/-- `F` vanishes identically near no point of `Re s > 0`. The witness is `F(½) ≠ 0`. -/
theorem etaTailLimit_not_eventually_zero {ρ : ℂ} (hρ : 0 < ρ.re) :
    ¬ (∀ᶠ z in 𝓝 ρ, etaTailLimit z = 0) := by
  intro hev
  have hev' : etaTailLimit =ᶠ[𝓝 ρ] 0 := by
    filter_upwards [hev] with z hz
    simpa using hz
  have hpre : IsPreconnected {s : ℂ | 0 < s.re} := (convex_halfSpace_re_gt (0 : ℝ)).isPreconnected
  have hzero := etaTailLimit_analyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero hpre hρ hev'
  have hhalf : (1 / 2 : ℂ) ∈ {s : ℂ | 0 < s.re} := by
    show (0 : ℝ) < (1 / 2 : ℂ).re
    norm_num
  exact etaTailLimit_half_ne_zero (by simpa using hzero hhalf)

end CriticalLinePhasor.NativeNontriviality
