import RequestProject.PhragmenBV

/-!
# Continuity of the chain kernel: the last kernel-side hypothesis discharged

The BV converse at the pure-real chain kernel carried one named input: continuity of
`realChainKernelLog` on the positive ray.  This file compiles it, closing the kernel
side of the converse at **every** compiled chart family:

* `gammaRClock_continuousOn` — the Gaussian clock is continuous on the ray;
* `realChainProfile_continuous` — **the induction**: the signed-log profile
  `u ↦ K(e^{-u})` of the chain is continuous.  The cons step is the compiled
  weight exchange (`weighted_logMellinConvolution_eq_convolution` at weight `1`):
  the weighted head profile is integrable (`mellinConvergent_iff_negLogIntegrable`
  + the compiled clock Mellin), the weighted tail profile is bounded (compiled) and
  continuous (induction), so Mathlib's
  `BddAbove.continuous_convolution_right_of_integrable` applies;
* `realChainKernelLog_continuousOn` — transported through `x = e^{-(-log x)}`;
* `weil_converse_of_BV_realChain'` — **the discharged corollary**: at the Maass
  chart type the converse now consumes exactly the package and one boundedness
  constant — the same closed shape as the `Γℂ` chart.  Both compiled chart families
  are kernel-side hypothesis-free;
* `maass_converse_of_BV` — the named instance at the spectral chart
  `Γℝ(s+(r-2j)it)`: the Maass `Sym^r` converse from package + BV alone.

No `axiom`, no `sorry`.
-/

open Real Complex Set Filter Topology MeasureTheory Asymptotics

namespace CriticalLinePhasor.ChainKernelContinuity

open CriticalLinePhasor.GlobalHelix CriticalLinePhasor.CarrierTheta
open CriticalLinePhasor.RamifiedMechanism CriticalLinePhasor.WeilConverse
open CriticalLinePhasor.PhragmenBV CriticalLinePhasor.RealChainMechanism

/-! ## The clock and its signed-log profile -/

theorem gammaRClock_profile_continuous (d : ℂ) :
    Continuous (fun u : ℝ => gammaRClock d (Real.exp (-u))) := by
  unfold gammaRClock
  refine (continuous_const.mul ?_).mul ?_
  · refine continuous_iff_continuousAt.mpr fun u => ?_
    have h1 : ContinuousAt (fun a : ℝ => ((a : ℝ) : ℂ) ^ d) (Real.exp (-u)) :=
      Complex.continuousAt_ofReal_cpow_const (Real.exp (-u)) d
        (Or.inr (Real.exp_pos _).ne')
    have h2 : ContinuousAt (fun u : ℝ => Real.exp (-u)) u := by fun_prop
    show ContinuousAt
      ((fun a : ℝ => ((a : ℝ) : ℂ) ^ d) ∘ (fun u : ℝ => Real.exp (-u))) u
    exact ContinuousAt.comp h1 h2
  · fun_prop

theorem gammaRClock_continuousOn (d : ℂ) :
    ContinuousOn (gammaRClock d) (Set.Ioi 0) := by
  unfold gammaRClock
  refine (continuousOn_const.mul ?_).mul (by fun_prop)
  intro x hx
  have hxpos : (0 : ℝ) < x := Set.mem_Ioi.mp hx
  exact (Complex.continuousAt_ofReal_cpow_const x d
    (Or.inr hxpos.ne')).continuousWithinAt

/-! ## The chain profile, by induction through the compiled weight exchange -/

theorem realChainProfile_continuous (ds : List ℂ) :
    ∀ d : ℂ, 0 ≤ d.re → (∀ e ∈ ds, 0 ≤ e.re) →
      Continuous (fun u : ℝ => realChainKernelLog d ds (Real.exp (-u))) := by
  induction ds with
  | nil =>
      intro d _ _
      exact gammaRClock_profile_continuous d
  | cons e es ih =>
      intro d hd hds
      have he : 0 ≤ e.re := hds e (by simp)
      have hes : ∀ z ∈ es, 0 ≤ z.re := fun z hz => hds z (by simp [hz])
      have hFwInt : Integrable (fun v : ℝ =>
          Complex.exp (-(1 : ℂ) * v) * gammaRClock d (Real.exp (-v))) :=
        (mellinConvergent_iff_negLogIntegrable (gammaRClock d) 1).mp
          (gammaRClock_mellinConvergent d 1 (by
            simp only [Complex.add_re, Complex.one_re]
            linarith))
      have hGwBdd : BddAbove (Set.range fun v : ℝ =>
          ‖Complex.exp (-(1 : ℂ) * v) * realChainKernelLog e es (Real.exp (-v))‖) := by
        obtain ⟨B, hB0, hB⟩ := weightedRealChainKernelLog_bounded e es 1
          (by linarith) (fun z hz => by have := hes z hz; linarith)
        refine ⟨B, ?_⟩
        rintro b ⟨v, rfl⟩
        exact hB v
      have hGwCont : Continuous (fun v : ℝ =>
          Complex.exp (-(1 : ℂ) * v) * realChainKernelLog e es (Real.exp (-v))) :=
        (by fun_prop : Continuous fun v : ℝ => Complex.exp (-(1 : ℂ) * v)).mul
          (ih e he hes)
      have hconv := hGwBdd.continuous_convolution_right_of_integrable
        (ContinuousLinearMap.mul ℂ ℂ) hFwInt hGwCont
      have hkey : ∀ u : ℝ,
          realChainKernelLog d (e :: es) (Real.exp (-u))
            = Complex.exp ((1 : ℂ) * u) *
                MeasureTheory.convolution
                  (fun v : ℝ =>
                    Complex.exp (-(1 : ℂ) * v) * gammaRClock d (Real.exp (-v)))
                  (fun v : ℝ =>
                    Complex.exp (-(1 : ℂ) * v) *
                      realChainKernelLog e es (Real.exp (-v)))
                  (ContinuousLinearMap.mul ℂ ℂ) MeasureTheory.volume u := by
        intro u
        have hw := weighted_logMellinConvolution_eq_convolution
          (gammaRClock d) (realChainKernelLog e es) 1 u
        have h3 : Complex.exp ((1 : ℂ) * u) * Complex.exp (-(1 : ℂ) * u) = 1 := by
          rw [← Complex.exp_add]
          simp
        calc realChainKernelLog d (e :: es) (Real.exp (-u))
            = logMellinConvolution (gammaRClock d) (realChainKernelLog e es)
                (Real.exp (-u)) := rfl
          _ = (Complex.exp ((1 : ℂ) * u) * Complex.exp (-(1 : ℂ) * u)) *
                logMellinConvolution (gammaRClock d) (realChainKernelLog e es)
                  (Real.exp (-u)) := by
              rw [h3, one_mul]
          _ = Complex.exp ((1 : ℂ) * u) *
                (Complex.exp (-(1 : ℂ) * u) *
                  logMellinConvolution (gammaRClock d) (realChainKernelLog e es)
                    (Real.exp (-u))) := by ring
          _ = _ := by rw [hw]
      exact ((by fun_prop : Continuous fun u : ℝ =>
        Complex.exp ((1 : ℂ) * u)).mul hconv).congr fun u => (hkey u).symm

/-- **Continuity of the chain kernel on the positive ray** — the last kernel-side
hypothesis of the BV converse, discharged. -/
theorem realChainKernelLog_continuousOn (d : ℂ) (hd : 0 ≤ d.re) (ds : List ℂ)
    (hds : ∀ e ∈ ds, 0 ≤ e.re) :
    ContinuousOn (realChainKernelLog d ds) (Set.Ioi 0) := by
  have hprof := realChainProfile_continuous ds d hd hds
  have hcomp : ContinuousOn
      (fun x : ℝ => realChainKernelLog d ds (Real.exp (-(-Real.log x))))
      (Set.Ioi 0) := by
    refine hprof.comp_continuousOn ?_
    exact (Real.continuousOn_log.mono (fun x hx =>
      (ne_of_gt (Set.mem_Ioi.mp hx)))).neg
  refine ContinuousOn.congr hcomp fun x hx => ?_
  have hxpos : (0 : ℝ) < x := Set.mem_Ioi.mp hx
  rw [neg_neg, Real.exp_log hxpos]

/-! ## The kernel-side-closed converse at the Maass chart type -/

/-- **The BV converse at the pure-real chain, fully discharged**: package + one
boundedness constant.  Both compiled chart families now share this closed shape. -/
theorem weil_converse_of_BV_realChain' (P : CoefficientSurface)
    (hdual : ∀ n : ℕ, P.adual n = P.a n)
    (d : ℂ) (hd : 0 ≤ d.re) (ds : List ℂ) (hds : ∀ e ∈ ds, 0 ≤ e.re)
    (ε : ℂ)
    (pkg : KNicePackage (coefficientArithmetic P.a)
      (realChainMellinKernel d hd ds hds).G
      (max (realChainMellinKernel d hd ds hds).B0 ((P.A : ℝ) + 1)) ε)
    (σ : ℝ) (hσ : max (realChainMellinKernel d hd ds hds).B0 ((P.A : ℝ) + 1) < σ)
    (C : ℝ) (hBV : ∀ z : ℂ, 1 - σ ≤ z.re → z.re ≤ σ → ‖pkg.lam z‖ ≤ C) :
    ∀ x : ℝ, 0 < x →
      coeffPrimal3DBankReadout P.a (realChainMellinKernel d hd ds hds).K (1 / x) =
        (ε * ((x ^ (1 : ℝ) : ℝ) : ℂ)) •
          coeffDual3DTransformedReadout P.adual
            (realChainMellinKernel d hd ds hds).K (1 / x) :=
  weil_converse_of_BV_realChain P hdual d hd ds hds
    (realChainKernelLog_continuousOn d hd ds hds) ε pkg σ hσ C hBV

/-- **The Maass converse from package + BV alone** — the named instance at the
spectral chart `∏ⱼ Γℝ(s + (r-2j)it)` of `Sym^r`, every rank, every spectral
parameter: the analytic package with one boundedness constant forces the theta
reflection of the bank. -/
theorem maass_converse_of_BV (P : CoefficientSurface)
    (hdual : ∀ n : ℕ, P.adual n = P.a n) (r : ℕ) (t : ℝ)
    (ε : ℂ)
    (pkg : KNicePackage (coefficientArithmetic P.a)
      (realChainMellinKernel (maassHead r t) (le_of_eq (maassHead_re r t).symm)
        (maassTail r t) (fun e he => le_of_eq (maassTail_re r t e he).symm)).G
      (max (realChainMellinKernel (maassHead r t) (le_of_eq (maassHead_re r t).symm)
        (maassTail r t) (fun e he => le_of_eq (maassTail_re r t e he).symm)).B0
        ((P.A : ℝ) + 1)) ε)
    (σ : ℝ)
    (hσ : max (realChainMellinKernel (maassHead r t) (le_of_eq (maassHead_re r t).symm)
      (maassTail r t) (fun e he => le_of_eq (maassTail_re r t e he).symm)).B0
      ((P.A : ℝ) + 1) < σ)
    (C : ℝ) (hBV : ∀ z : ℂ, 1 - σ ≤ z.re → z.re ≤ σ → ‖pkg.lam z‖ ≤ C) :
    ∀ x : ℝ, 0 < x →
      coeffPrimal3DBankReadout P.a
        (realChainMellinKernel (maassHead r t) (le_of_eq (maassHead_re r t).symm)
          (maassTail r t) (fun e he => le_of_eq (maassTail_re r t e he).symm)).K
        (1 / x) =
        (ε * ((x ^ (1 : ℝ) : ℝ) : ℂ)) •
          coeffDual3DTransformedReadout P.adual
            (realChainMellinKernel (maassHead r t)
              (le_of_eq (maassHead_re r t).symm) (maassTail r t)
              (fun e he => le_of_eq (maassTail_re r t e he).symm)).K (1 / x) :=
  weil_converse_of_BV_realChain' P hdual (maassHead r t)
    (le_of_eq (maassHead_re r t).symm) (maassTail r t)
    (fun e he => le_of_eq (maassTail_re r t e he).symm) ε pkg σ hσ C hBV

end CriticalLinePhasor.ChainKernelContinuity

#print axioms CriticalLinePhasor.ChainKernelContinuity.realChainProfile_continuous
#print axioms CriticalLinePhasor.ChainKernelContinuity.realChainKernelLog_continuousOn
#print axioms CriticalLinePhasor.ChainKernelContinuity.weil_converse_of_BV_realChain'
#print axioms CriticalLinePhasor.ChainKernelContinuity.maass_converse_of_BV
