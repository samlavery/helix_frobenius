import RequestProject.PrimeClockCentered
import RequestProject.CarrierChannelReadout
import RequestProject.LFunctionPhasor

/-!
# An ordered eta bank for the logarithmic derivative

The prime-clock carrier is constant in the rank, so its corridor convergence
reduces to convergence of the prime-ordered logarithmic-derivative series.
This file constructs the comparison bank whose finite stages come from the
locally uniformly convergent Abel tail of the eta series.

Search audit:

```
rg -n -i 'etaPartial.*deriv|deriv.*etaPartial|logDeriv.*etaPartial' \
  RequestProject .lake/packages/mathlib/Mathlib --glob '*.lean'
rg -n 'eta_summableLocallyUniformlyOn_tail|eta_partialSum_tendsto_tail' \
  RequestProject --glob '*.lean'
rg -n 'logDeriv_tendsto|hasSumLocallyUniformlyOn_iff' \
  .lake/packages/mathlib/Mathlib --glob '*.lean'
```
-/

open Complex Filter Topology

noncomputable section

namespace CriticalLinePhasor.BankNoTransient

/-- The Abel-summation tail term for the ordered eta series. -/
def etaTailTerm (i : ℕ) (s : ℂ) : ℂ :=
  -(((i : ℂ) + 1) ^ (-s) - (i : ℂ) ^ (-s)) *
    ∑ j ∈ Finset.range (i + 1), (-1 : ℂ) ^ (j + 1)

/-- The first `N` terms of the eta Abel tail. -/
def etaTailPartial (N : ℕ) (s : ℂ) : ℂ :=
  ∑ i ∈ Finset.range N, etaTailTerm i s

/-- The locally uniform limit of the eta Abel tail. -/
def etaTailLimit (s : ℂ) : ℂ := ∑' i : ℕ, etaTailTerm i s

/-- The finite eta tails converge locally uniformly throughout `Re s > 0`. -/
theorem etaTailPartial_tendstoLocallyUniformlyOn :
    TendstoLocallyUniformlyOn etaTailPartial etaTailLimit atTop
      {s : ℂ | 0 < s.re} := by
  have hs :=
    CriticalLinePhasor.LFunctionPhasor.eta_summableLocallyUniformlyOn_tail
  have hfin := hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp
    hs.hasSumLocallyUniformlyOn
  intro u hu x hx
  obtain ⟨t, ht, hev⟩ := hfin u hu x hx
  refine ⟨t, ht, ?_⟩
  filter_upwards [tendsto_finset_range.eventually hev] with N hN
  simpa [etaTailPartial, etaTailLimit, etaTailTerm] using hN

/-- The eta tail limit is the standard eta factor times zeta. -/
theorem etaTailLimit_eq_etaProduct {u : ℂ} (hu : 0 < u.re)
    (hu1 : u ≠ 1) :
    etaTailLimit u =
      (1 - (2 : ℂ) ^ ((1 : ℂ) - u)) * riemannZeta u := by
  have htail :=
    CriticalLinePhasor.LFunctionPhasor.eta_partialSum_tendsto_tail hu
  have hprod := CriticalLinePhasor.LFunctionPhasor.eta_strip_tendsto hu hu1
  have h := tendsto_nhds_unique htail hprod
  simpa [etaTailLimit, etaTailTerm] using h

/-- Local uniform convergence differentiates and passes to logarithmic
derivatives at every nonzero limit point. -/
theorem etaTailPartial_logDeriv_tendsto {u : ℂ}
    (hu : 0 < u.re) (hne : etaTailLimit u ≠ 0) :
    Tendsto (fun N => logDeriv (etaTailPartial N) u) atTop
      (nhds (logDeriv etaTailLimit u)) := by
  have hopen : IsOpen {s : ℂ | 0 < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  apply Complex.logDeriv_tendsto hopen hu
    etaTailPartial_tendstoLocallyUniformlyOn
  · exact Eventually.of_forall fun N z hz => by
      apply DifferentiableAt.differentiableWithinAt
      apply DifferentiableAt.fun_sum
      intro i hi
      exact
        CriticalLinePhasor.LFunctionPhasor.eta_differentiableAt_tailSummand
          i z hz
  · exact hne

/-- The eta tail and the compiled carrier eta limit agree near every point
of the punctured right half-plane. -/
theorem etaTailLimit_eventuallyEq_etaLim {u : ℂ}
    (hu : 0 < u.re) (hu1 : u ≠ 1) :
    etaTailLimit =ᶠ[nhds u] CriticalLinePhasor.DVP.etaLim := by
  have hopen : IsOpen ({z : ℂ | 0 < z.re} \ {1}) :=
    (isOpen_lt continuous_const Complex.continuous_re).sdiff
      isClosed_singleton
  have humem : u ∈ ({z : ℂ | 0 < z.re} \ {1}) := ⟨hu, hu1⟩
  filter_upwards [hopen.mem_nhds humem] with z hz
  rw [etaTailLimit_eq_etaProduct hz.1 hz.2,
    CriticalLinePhasor.DVP.etaLim_eq_zeta hz.1 hz.2]

/-- Consequently their logarithmic derivatives agree. -/
theorem logDeriv_etaTailLimit_eq_etaLim {u : ℂ}
    (hu : 0 < u.re) (hu1 : u ≠ 1) :
    logDeriv etaTailLimit u =
      logDeriv CriticalLinePhasor.DVP.etaLim u := by
  have hev := etaTailLimit_eventuallyEq_etaLim hu hu1
  rw [logDeriv_apply, logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds]

/-- The finite eta logarithmic-derivative readout with its explicit factor
removed. -/
def etaZetaLogDerivPartial (N : ℕ) (u : ℂ) : ℂ :=
  logDeriv (etaTailPartial N) u -
    logDeriv (fun w => (1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - w)) u

/-- Away from a zeta zero, the finite eta readout converges to `ζ'/ζ` on
the entire strip `0 < Re u < 1`. -/
theorem etaZetaLogDerivPartial_tendsto {u : ℂ}
    (hu : 0 < u.re) (hu1 : u.re < 1) (hz : riemannZeta u ≠ 0) :
    Tendsto (fun N => etaZetaLogDerivPartial N u) atTop
      (nhds (logDeriv riemannZeta u)) := by
  have hune : u ≠ 1 := by
    intro h
    rw [h] at hu1
    simp at hu1
  have htailne : etaTailLimit u ≠ 0 := by
    rw [etaTailLimit_eq_etaProduct hu hune]
    exact mul_ne_zero
      (CriticalLinePhasor.CarrierChannelReadout.etaFactor_ne_zero hu1) hz
  let c : ℂ :=
    logDeriv (fun w => (1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - w)) u
  have hc : Tendsto (fun _ : ℕ => c) atTop (nhds c) :=
    tendsto_const_nhds
  have h := (etaTailPartial_logDeriv_tendsto hu htailne).sub hc
  have hread :=
    CriticalLinePhasor.CarrierChannelReadout.zeta_logDeriv_eq_etaLim
      hu hu1 hz
  rw [← logDeriv_etaTailLimit_eq_etaLim hu hune] at hread
  rw [hread]
  simpa [etaZetaLogDerivPartial, c] using h

/-- The eta readout transported back to the xi chart. -/
def etaXiBank (N : ℕ) (s : ℂ) : ℂ :=
  etaZetaLogDerivPartial N ((1 / 2 : ℂ) - s) +
    xiCarrierCorrection s

/-- Away from a reflected zeta zero, the eta bank converges to the completed
xi logarithmic derivative. -/
theorem etaXiBank_tendsto {s : ℂ}
    (hu0 : 0 < ((1 / 2 : ℂ) - s).re)
    (hu1 : ((1 / 2 : ℂ) - s).re < 1)
    (hz : riemannZeta ((1 / 2 : ℂ) - s) ≠ 0) :
    Tendsto (fun N => etaXiBank N s) atTop
      (nhds (logDeriv ZD.riemannXi s)) := by
  have h := etaZetaLogDerivPartial_tendsto hu0 hu1 hz
  have hc : Tendsto (fun _ : ℕ => xiCarrierCorrection s) atTop
      (nhds (xiCarrierCorrection s)) := tendsto_const_nhds
  have hadd := h.add hc
  have hlim :
      logDeriv riemannZeta ((1 / 2 : ℂ) - s) +
          xiCarrierCorrection s =
        logDeriv ZD.riemannXi s := by
    simp [xiCarrierCorrection]
  rw [hlim] at hadd
  simpa [etaXiBank] using hadd

/-- The eta bank reaches every point of the stated `634.5` channel once the
reflected zeta value at that point is nonzero. -/
theorem etaXiBank_tendsto_on_channel {s : ℂ}
    (him : 1269 / 2 < |s.im|)
    (hlow : 1 / (Real.log |s.im|) ^ 9 < s.re)
    (hhigh : s.re < 1 / 2)
    (hz : riemannZeta ((1 / 2 : ℂ) - s) ≠ 0) :
    Tendsto (fun N => etaXiBank N s) atTop
      (nhds (logDeriv ZD.riemannXi s)) := by
  have habs : 1 < |s.im| := lt_trans (by norm_num) him
  have hlog : 0 < Real.log |s.im| := Real.log_pos habs
  have hden : 0 < (Real.log |s.im|) ^ 9 := pow_pos hlog 9
  have hfrac : 0 < 1 / (Real.log |s.im|) ^ 9 := one_div_pos.mpr hden
  have hs0 : 0 < s.re := lt_trans hfrac hlow
  apply etaXiBank_tendsto
  · norm_num [Complex.sub_re, Complex.div_re]
    linarith
  · norm_num [Complex.sub_re, Complex.div_re]
    linarith
  · exact hz

end CriticalLinePhasor.BankNoTransient

#print axioms CriticalLinePhasor.BankNoTransient.etaTailPartial_tendstoLocallyUniformlyOn
#print axioms CriticalLinePhasor.BankNoTransient.etaTailLimit_eq_etaProduct
#print axioms CriticalLinePhasor.BankNoTransient.etaTailPartial_logDeriv_tendsto
#print axioms CriticalLinePhasor.BankNoTransient.etaZetaLogDerivPartial_tendsto
#print axioms CriticalLinePhasor.BankNoTransient.etaXiBank_tendsto
#print axioms CriticalLinePhasor.BankNoTransient.etaXiBank_tendsto_on_channel
