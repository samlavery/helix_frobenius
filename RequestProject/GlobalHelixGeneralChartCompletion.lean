import RequestProject.GlobalHelixRealClockCompletion

/-!
# The general Deligne chart: arbitrary real/complex completion kernels

The complex-place kernel (`completionKernelLog`, multiplier `∏Γℂ`) and the single-real
mixed kernel (`mixedKernelLog`, multiplier `Γℝ·∏Γℂ`) generalize to the full Deligne
chart: an arbitrary finite list of real clocks convolved in signed-log height onto the
complex-pair kernel.

* `generalKernelLog dlts μs` — the kernel with Mellin multiplier
  `∏ⱼΓℝ(s+δⱼ)·∏ᵢΓℂ(s+μᵢ)` (`generalKernelLog_hasMellin`), uniformly bounded at every
  admissible weight (`weightedGeneralKernelLog_bounded`), rapidly decreasing
  (`generalKernelLog_rapid`) — by one induction over the real-shift list, whose base is
  the compiled complex kernel and whose step is the compiled real clock;
* `generalPrimal3DBankReadout` / `generalDual3DTransformedReadout` — the primal and
  reciprocal-height contragredient 3D banks carrying the general kernel, equal to
  coefficient theta functions on the positive carrier, locally integrable, rapidly
  decreasing;
* `generalPrimal3D_initialIdentification` / `generalDual3D_initialIdentification` — on
  the initial half-plane the Mellin transforms of both banks are the completed readouts
  `∏Γℝ·∏Γℂ·D(s)`.

`generalKernelLog [] μs` is definitionally the complex kernel and
`generalKernelLog [δ] μs` the mixed kernel, so this file strictly subsumes both compiled
chart types.  No `axiom`, no `sorry`.
-/

open Finset ArithmeticFunction Complex UpperHalfPlane

namespace CriticalLinePhasor.GlobalHelix

open CriticalLinePhasor.CarrierTheta ConeProjection
open Set Filter Topology MeasureTheory Asymptotics

variable {ι : Type*} [Fintype ι]

/-- The general archimedean kernel: a finite list of real clocks convolved in signed-log
height onto the complex-pair completion kernel — Mellin multiplier
`∏ⱼΓℝ(s+δⱼ)·∏ᵢΓℂ(s+μᵢ)`, the general Deligne chart. -/
noncomputable def generalKernelLog : List ℂ → List ℂ → ℝ → ℂ
  | [], μs => completionKernelLog μs
  | dlt :: dlts, μs => logMellinConvolution (gammaRClock dlt) (generalKernelLog dlts μs)

/-- The empty real-shift list is definitionally the complex-pair kernel. -/
theorem generalKernelLog_nil (μs : List ℂ) :
    generalKernelLog [] μs = completionKernelLog μs := rfl

/-- A singleton real-shift list is definitionally the mixed kernel. -/
theorem generalKernelLog_singleton (dlt : ℂ) (μs : List ℂ) :
    generalKernelLog [dlt] μs = mixedKernelLog dlt μs := rfl

/-- A common sufficiently positive Mellin weight bounds the general kernel uniformly. -/
theorem weightedGeneralKernelLog_bounded (dlts μs : List ℂ) (hne : μs ≠ []) (s : ℝ)
    (hdlts : ∀ dlt ∈ dlts, 0 < s + dlt.re) (hs : ∀ μ ∈ μs, 0 < s + μ.re) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ u : ℝ,
      ‖Complex.exp (-(s : ℂ) * u) * generalKernelLog dlts μs (Real.exp (-u))‖ ≤ B := by
  induction dlts with
  | nil => exact weightedCompletionKernelLog_bounded μs hne s hs
  | cons dlt dlts ih =>
      obtain ⟨B, hB, hbound⟩ := ih (fun z hz => hdlts z (by simp [hz]))
      let F : ℝ → ℂ := fun u =>
        Complex.exp (-(s : ℂ) * u) * gammaRClock dlt (Real.exp (-u))
      let G : ℝ → ℂ := fun u =>
        Complex.exp (-(s : ℂ) * u) * generalKernelLog dlts μs (Real.exp (-u))
      have hsdlt : 0 < (((s : ℝ) : ℂ) + dlt).re := by
        simpa using hdlts dlt (by simp)
      have hF : Integrable F :=
        (mellinConvergent_iff_negLogIntegrable (gammaRClock dlt) (s : ℂ)).mp
          (gammaRClock_mellinConvergent dlt (s : ℂ) hsdlt)
      refine ⟨B * ∫ u : ℝ, ‖F u‖,
        mul_nonneg hB (integral_nonneg fun _ => norm_nonneg _), ?_⟩
      intro u
      rw [show generalKernelLog (dlt :: dlts) μs
          = logMellinConvolution (gammaRClock dlt) (generalKernelLog dlts μs) from rfl,
        weighted_logMellinConvolution_eq_convolution]
      exact norm_convolution_mul_le_of_integrable_of_bound F G hF B hbound u

/-- The general kernel decreases faster than every real power at positive infinity. -/
theorem generalKernelLog_rapid (dlts μs : List ℂ) (hne : μs ≠ []) :
    ∀ q : ℝ, generalKernelLog dlts μs =O[atTop] (fun x : ℝ => x ^ q) := by
  intro q
  obtain ⟨s, hsq, hall⟩ := exists_weight_gt_neg_and_shifts q (dlts ++ μs)
  have hdlts : ∀ dlt ∈ dlts, 0 < s + dlt.re := by
    intro z hz
    linarith [hall z (by simp [hz])]
  have hspos : ∀ μ ∈ μs, 0 < s + μ.re := by
    intro μ hμ
    linarith [hall μ (by simp [hμ])]
  obtain ⟨B, hB, hbound⟩ :=
    weightedGeneralKernelLog_bounded dlts μs hne s hdlts hspos
  rw [Asymptotics.isBigO_iff']
  refine ⟨B + 1, by linarith, ?_⟩
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx1
  have hx : 0 < x := zero_lt_one.trans hx1
  have hexponent :
      (-(s : ℂ) * ((-Real.log x : ℝ) : ℂ)).re = s * Real.log x := by
    norm_num
  have hweight :
      ‖Complex.exp (-(s : ℂ) * ((-Real.log x : ℝ) : ℂ))‖ = x ^ s := by
    rw [Complex.norm_exp, hexponent, Real.rpow_def_of_pos hx]
    congr 1
    ring
  have hraw := hbound (-Real.log x)
  have hexp : Real.exp (-(-Real.log x)) = x := by
    rw [neg_neg, Real.exp_log hx]
  rw [hexp, norm_mul, hweight] at hraw
  have hraw' : ‖generalKernelLog dlts μs x‖ * x ^ s ≤ B := by
    simpa [mul_comm] using hraw
  have hpow : 0 < x ^ s := Real.rpow_pos_of_pos hx s
  have hk : ‖generalKernelLog dlts μs x‖ ≤ B * x ^ (-s) := by
    have hdiv := (le_div_iff₀ hpow).2 hraw'
    rwa [div_eq_mul_inv, ← Real.rpow_neg hx.le] at hdiv
  calc
    ‖generalKernelLog dlts μs x‖ ≤ B * x ^ (-s) := hk
    _ ≤ (B + 1) * x ^ (-s) := by gcongr; linarith
    _ ≤ (B + 1) * x ^ q := by
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith : -s ≤ q))
        (by linarith)
    _ = (B + 1) * ‖x ^ q‖ := by
      rw [Real.norm_of_nonneg (Real.rpow_nonneg hx.le q)]

/-- **The general kernel has exactly the general Deligne multiplier.** -/
theorem generalKernelLog_hasMellin (dlts μs : List ℂ) (hne : μs ≠ []) (s : ℂ)
    (hdlts : ∀ dlt ∈ dlts, 0 < (s + dlt).re) (hs : ∀ μ ∈ μs, 0 < (s + μ).re) :
    HasMellin (generalKernelLog dlts μs) s
      ((dlts.map fun dlt => Complex.Gammaℝ (s + dlt)).prod *
        (μs.map fun μ => Complex.Gammaℂ (s + μ)).prod) := by
  induction dlts with
  | nil =>
      simpa [generalKernelLog] using completionKernelLog_hasMellin μs hne s hs
  | cons dlt dlts ih =>
      have hR : HasMellin (gammaRClock dlt) s (Complex.Gammaℝ (s + dlt)) :=
        ⟨gammaRClock_mellinConvergent dlt s (hdlts dlt (by simp)),
          gammaRClock_mellin dlt s (hdlts dlt (by simp))⟩
      have htail := ih (fun z hz => hdlts z (by simp [hz]))
      have hconv := logMellinConvolution_hasMellin (gammaRClock dlt)
        (generalKernelLog dlts μs) s hR.1 htail.1
      rw [show generalKernelLog (dlt :: dlts) μs
          = logMellinConvolution (gammaRClock dlt) (generalKernelLog dlts μs) from rfl]
      refine ⟨hconv.1, ?_⟩
      rw [hconv.2, hR.2, htail.2, List.map_cons, List.prod_cons]
      ring

variable {ι : Type*} [Fintype ι]

/-- The primal 3D bank carrying the general archimedean kernel. -/
noncomputable def generalPrimal3DBankReadout (W : PolynomialSatakeDualPair ι)
    (dlts μs : List ℂ) (x : ℝ) : ℂ :=
  ∑' n : ℕ,
    fiberPhasor (coefficientFiber (cpsPolynomialPrimalCoeff W) n x) *
      generalKernelLog dlts μs
        (multiplicativeHeight (coefficientFiber (cpsPolynomialPrimalCoeff W) n x))

/-- The reciprocal-height contragredient 3D bank with the general kernel. -/
noncomputable def generalDual3DTransformedReadout (W : PolynomialSatakeDualPair ι)
    (dlts μs : List ℂ) (x : ℝ) : ℂ :=
  ∑' n : ℕ,
    fiberPhasor
        (reciprocalCoefficientFiber
          (fun j => (starRingEnd ℂ) (cpsPolynomialDualCoeff W j)) n x) *
      generalKernelLog dlts μs
        (multiplicativeHeight
          (reciprocalCoefficientFiber
            (fun j => (starRingEnd ℂ) (cpsPolynomialDualCoeff W j)) n x))

theorem generalPrimal3DBankReadout_eq_theta (W : PolynomialSatakeDualPair ι)
    (dlts μs : List ℂ) {x : ℝ} (hx : 0 < x) :
    generalPrimal3DBankReadout W dlts μs x =
      theta (cpsPolynomialPrimalCoeff W) (generalKernelLog dlts μs) x := by
  unfold generalPrimal3DBankReadout theta
  apply tsum_congr
  intro n
  rw [fiberPhasor_coefficientFiber,
    multiplicativeHeight_coefficientFiber (cpsPolynomialPrimalCoeff W) n hx]

theorem generalDual3DTransformedReadout_eq_theta_one_div (W : PolynomialSatakeDualPair ι)
    (dlts μs : List ℂ) {x : ℝ} (hx : 0 < x) :
    generalDual3DTransformedReadout W dlts μs x =
      theta (cpsPolynomialDualCoeff W) (generalKernelLog dlts μs) (1 / x) := by
  unfold generalDual3DTransformedReadout theta
  apply tsum_congr
  intro n
  rw [fiberPhasor_reciprocalCoefficientFiber_conj,
    multiplicativeHeight_reciprocalCoefficientFiber _ n hx]
  simp [div_eq_mul_inv]

/-- At unit conductor the scaled complex kernel is the complex kernel. -/
theorem conductorScaledCompletionKernelLog_one (μs : List ℂ) :
    conductorScaledCompletionKernelLog 1 μs = completionKernelLog μs := by
  funext x
  unfold conductorScaledCompletionKernelLog
  rw [div_one]

/-- The empty-real-list primal 3D bank is the compiled complex-chart 3D bank at unit
conductor. -/
theorem generalPrimal3DBankReadout_nil (W : PolynomialSatakeDualPair ι) (μs : List ℂ) :
    generalPrimal3DBankReadout W [] μs
      = cpsPolynomialFullPrimal3DBankReadout W 1 μs := by
  funext x
  unfold generalPrimal3DBankReadout cpsPolynomialFullPrimal3DBankReadout
  simp only [generalKernelLog_nil, conductorScaledCompletionKernelLog_one]

/-- The empty-real-list contragredient 3D bank is the compiled complex-chart one. -/
theorem generalDual3DTransformedReadout_nil (W : PolynomialSatakeDualPair ι)
    (μs : List ℂ) :
    generalDual3DTransformedReadout W [] μs
      = cpsPolynomialFullDual3DTransformedReadout W 1 μs := by
  funext x
  unfold generalDual3DTransformedReadout cpsPolynomialFullDual3DTransformedReadout
  simp only [generalKernelLog_nil, conductorScaledCompletionKernelLog_one]

/-- The singleton-real-list primal 3D bank is definitionally the mixed one. -/
theorem generalPrimal3DBankReadout_singleton (W : PolynomialSatakeDualPair ι)
    (dlt : ℂ) (μs : List ℂ) :
    generalPrimal3DBankReadout W [dlt] μs = mixedPrimal3DBankReadout W dlt μs := rfl

/-- The singleton-real-list contragredient 3D bank is definitionally the mixed one. -/
theorem generalDual3DTransformedReadout_singleton (W : PolynomialSatakeDualPair ι)
    (dlt : ℂ) (μs : List ℂ) :
    generalDual3DTransformedReadout W [dlt] μs
      = mixedDual3DTransformedReadout W dlt μs := rfl

/-- One admissible common Mellin weight for the general chart and both banks. -/
theorem exists_general_weight (q : ℝ) (dlts μs : List ℂ) :
    ∃ σ : ℝ, -q < σ ∧ (∀ dlt ∈ dlts, 0 < σ + dlt.re) ∧ ∀ μ ∈ μs, 0 < σ + μ.re := by
  obtain ⟨σ, hσq, hσ⟩ := exists_weight_gt_neg_and_shifts q (dlts ++ μs)
  exact ⟨σ, hσq, fun z hz => by linarith [hσ z (by simp [hz])],
    fun μ hμ => by linarith [hσ μ (by simp [hμ])]⟩

theorem generalPrimalTheta_locallyIntegrableOn (W : PolynomialSatakeDualPair ι)
    (dlts μs : List ℂ) (hne : μs ≠ []) :
    MeasureTheory.LocallyIntegrableOn
      (theta (cpsPolynomialPrimalCoeff W) (generalKernelLog dlts μs))
      (Set.Ioi 0) := by
  let A : ℝ := (Fintype.card ι + W.primalExponent : ℕ)
  obtain ⟨σ, hσA, hσdlts, hσμ⟩ := exists_general_weight (-(A + 1)) dlts μs
  have hA : A + 1 < ((σ : ℂ).re) := by simpa using hσA
  have hdlts : ∀ dlt ∈ dlts, 0 < (((σ : ℂ) + dlt).re) := by
    intro z hz
    simp only [Complex.add_re, Complex.ofReal_re]
    exact hσdlts z hz
  have hμ : ∀ μ ∈ μs, 0 < (((σ : ℂ) + μ).re) := by
    intro μ hμs
    simp only [Complex.add_re, Complex.ofReal_re]
    exact hσμ μ hμs
  have ha : ∀ n : ℕ, ‖cpsPolynomialPrimalCoeff W n‖ ≤
      (1 : ℝ) * (((n + 1 : ℕ) : ℝ) ^ A) := by
    intro n
    change ‖cpsPolynomialPrimalCoeff W n‖ ≤
      1 * (((n + 1 : ℕ) : ℝ) ^
        ((Fintype.card ι + W.primalExponent : ℕ) : ℝ))
    rw [one_mul, Real.rpow_natCast]
    exact cpsPolynomialPrimalCoeff_norm_le W n
  have hg := generalKernelLog_hasMellin dlts μs hne (σ : ℂ) hdlts hμ
  have htheta := theta_hasMellin_of_polynomial
    (cpsPolynomialPrimalCoeff W) (generalKernelLog dlts μs)
      (σ : ℂ) 1 A hg.1 ha hA
  exact locallyIntegrableOn_of_mellinConvergent _ _ htheta.1

theorem generalDualTheta_locallyIntegrableOn (W : PolynomialSatakeDualPair ι)
    (dlts μs : List ℂ) (hne : μs ≠ []) :
    MeasureTheory.LocallyIntegrableOn
      (theta (cpsPolynomialDualCoeff W) (generalKernelLog dlts μs))
      (Set.Ioi 0) := by
  let A : ℝ := (Fintype.card ι + W.dualExponent : ℕ)
  obtain ⟨σ, hσA, hσdlts, hσμ⟩ := exists_general_weight (-(A + 1)) dlts μs
  have hA : A + 1 < ((σ : ℂ).re) := by simpa using hσA
  have hdlts : ∀ dlt ∈ dlts, 0 < (((σ : ℂ) + dlt).re) := by
    intro z hz
    simp only [Complex.add_re, Complex.ofReal_re]
    exact hσdlts z hz
  have hμ : ∀ μ ∈ μs, 0 < (((σ : ℂ) + μ).re) := by
    intro μ hμs
    simp only [Complex.add_re, Complex.ofReal_re]
    exact hσμ μ hμs
  have ha : ∀ n : ℕ, ‖cpsPolynomialDualCoeff W n‖ ≤
      (1 : ℝ) * (((n + 1 : ℕ) : ℝ) ^ A) := by
    intro n
    change ‖cpsPolynomialDualCoeff W n‖ ≤
      1 * (((n + 1 : ℕ) : ℝ) ^
        ((Fintype.card ι + W.dualExponent : ℕ) : ℝ))
    rw [one_mul, Real.rpow_natCast]
    exact cpsPolynomialDualCoeff_norm_le W n
  have hg := generalKernelLog_hasMellin dlts μs hne (σ : ℂ) hdlts hμ
  have htheta := theta_hasMellin_of_polynomial
    (cpsPolynomialDualCoeff W) (generalKernelLog dlts μs)
      (σ : ℂ) 1 A hg.1 ha hA
  exact locallyIntegrableOn_of_mellinConvergent _ _ htheta.1

theorem generalPrimal3DBankReadout_locallyIntegrableOn (W : PolynomialSatakeDualPair ι)
    (dlts μs : List ℂ) (hne : μs ≠ []) :
    MeasureTheory.LocallyIntegrableOn (generalPrimal3DBankReadout W dlts μs)
      (Set.Ioi 0) := by
  apply MeasureTheory.LocallyIntegrableOn.congr _
    (generalPrimalTheta_locallyIntegrableOn W dlts μs hne)
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
  exact (generalPrimal3DBankReadout_eq_theta W dlts μs hx).symm

theorem generalDual3DReflectedReadout_locallyIntegrableOn (W : PolynomialSatakeDualPair ι)
    (dlts μs : List ℂ) (hne : μs ≠ []) :
    MeasureTheory.LocallyIntegrableOn
      (fun x : ℝ => generalDual3DTransformedReadout W dlts μs (1 / x)) (Set.Ioi 0) := by
  apply MeasureTheory.LocallyIntegrableOn.congr _
    (generalDualTheta_locallyIntegrableOn W dlts μs hne)
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
  have hxpos : 0 < x := Set.mem_Ioi.mp hx
  rw [generalDual3DTransformedReadout_eq_theta_one_div W dlts μs
    (one_div_pos.mpr hxpos)]
  simp

theorem generalPrimal3DBankReadout_rapid (W : PolynomialSatakeDualPair ι)
    (dlts μs : List ℂ) (hne : μs ≠ []) :
    ∀ q : ℝ, generalPrimal3DBankReadout W dlts μs =O[atTop] (fun x : ℝ => x ^ q) := by
  let A : ℝ := (Fintype.card ι + W.primalExponent : ℕ)
  have ha : ∀ n : ℕ, ‖cpsPolynomialPrimalCoeff W n‖ ≤
      (1 : ℝ) * (((n + 1 : ℕ) : ℝ) ^ A) := by
    intro n
    change ‖cpsPolynomialPrimalCoeff W n‖ ≤
      1 * (((n + 1 : ℕ) : ℝ) ^
        ((Fintype.card ι + W.primalExponent : ℕ) : ℝ))
    rw [one_mul, Real.rpow_natCast]
    exact cpsPolynomialPrimalCoeff_norm_le W n
  have htheta := theta_rapid_of_polynomial_of_kernel_rapid
    (cpsPolynomialPrimalCoeff W) (generalKernelLog dlts μs)
      1 A zero_le_one ha (generalKernelLog_rapid dlts μs hne)
  intro q
  have heq :
      theta (cpsPolynomialPrimalCoeff W)
          (generalKernelLog dlts μs) =ᶠ[atTop]
        generalPrimal3DBankReadout W dlts μs := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact (generalPrimal3DBankReadout_eq_theta W dlts μs hx).symm
  simpa using (htheta q).congr' heq Filter.EventuallyEq.rfl

theorem generalDual3DReflectedReadout_rapid (W : PolynomialSatakeDualPair ι)
    (dlts μs : List ℂ) (hne : μs ≠ []) :
    ∀ q : ℝ,
      (fun x : ℝ => generalDual3DTransformedReadout W dlts μs (1 / x))
        =O[atTop] (fun x : ℝ => x ^ q) := by
  let A : ℝ := (Fintype.card ι + W.dualExponent : ℕ)
  have ha : ∀ n : ℕ, ‖cpsPolynomialDualCoeff W n‖ ≤
      (1 : ℝ) * (((n + 1 : ℕ) : ℝ) ^ A) := by
    intro n
    change ‖cpsPolynomialDualCoeff W n‖ ≤
      1 * (((n + 1 : ℕ) : ℝ) ^
        ((Fintype.card ι + W.dualExponent : ℕ) : ℝ))
    rw [one_mul, Real.rpow_natCast]
    exact cpsPolynomialDualCoeff_norm_le W n
  have htheta := theta_rapid_of_polynomial_of_kernel_rapid
    (cpsPolynomialDualCoeff W) (generalKernelLog dlts μs)
      1 A zero_le_one ha (generalKernelLog_rapid dlts μs hne)
  intro q
  have heq :
      theta (cpsPolynomialDualCoeff W)
          (generalKernelLog dlts μs) =ᶠ[atTop]
        (fun x : ℝ => generalDual3DTransformedReadout W dlts μs (1 / x)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [generalDual3DTransformedReadout_eq_theta_one_div W dlts μs
      (one_div_pos.mpr hx)]
    simp
  simpa using (htheta q).congr' heq Filter.EventuallyEq.rfl

/-- The general completed readout. -/
noncomputable def generalPrimalCompletedReadout (W : PolynomialSatakeDualPair ι)
    (dlts μs : List ℂ) (s : ℂ) : ℂ :=
  (dlts.map fun dlt => Complex.Gammaℝ (s + dlt)).prod *
    (μs.map fun μ => Complex.Gammaℂ (s + μ)).prod *
    dirichlet (cpsPolynomialPrimalCoeff W) s

noncomputable def generalDualCompletedReadout (W : PolynomialSatakeDualPair ι)
    (dlts μs : List ℂ) (s : ℂ) : ℂ :=
  (dlts.map fun dlt => Complex.Gammaℝ (s + dlt)).prod *
    (μs.map fun μ => Complex.Gammaℂ (s + μ)).prod *
    dirichlet (cpsPolynomialDualCoeff W) s

theorem generalPrimal3D_initialIdentification (W : PolynomialSatakeDualPair ι)
    (dlts μs : List ℂ) (hne : μs ≠ []) (s : ℂ)
    (hdlts : ∀ dlt ∈ dlts, 0 < (s + dlt).re) (hμ : ∀ μ ∈ μs, 0 < (s + μ).re)
    (hs : ((Fintype.card ι + W.primalExponent : ℕ) : ℝ) + 1 < s.re) :
    mellin (generalPrimal3DBankReadout W dlts μs) s =
      generalPrimalCompletedReadout W dlts μs s := by
  have heq : mellin (generalPrimal3DBankReadout W dlts μs) s =
      mellin (theta (cpsPolynomialPrimalCoeff W)
        (generalKernelLog dlts μs)) s := by
    unfold mellin
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp only
    rw [generalPrimal3DBankReadout_eq_theta W dlts μs (Set.mem_Ioi.mp hx)]
  rw [heq]
  let A : ℝ := (Fintype.card ι + W.primalExponent : ℕ)
  have ha : ∀ n : ℕ, ‖cpsPolynomialPrimalCoeff W n‖ ≤
      (1 : ℝ) * (((n + 1 : ℕ) : ℝ) ^ A) := by
    intro n
    change ‖cpsPolynomialPrimalCoeff W n‖ ≤
      1 * (((n + 1 : ℕ) : ℝ) ^
        ((Fintype.card ι + W.primalExponent : ℕ) : ℝ))
    rw [one_mul, Real.rpow_natCast]
    exact cpsPolynomialPrimalCoeff_norm_le W n
  have hg := generalKernelLog_hasMellin dlts μs hne s hdlts hμ
  have h := theta_hasMellin_of_polynomial
    (cpsPolynomialPrimalCoeff W) (generalKernelLog dlts μs)
      s 1 A hg.1 ha (by simpa [A] using hs)
  rw [h.2, hg.2]
  unfold generalPrimalCompletedReadout
  ring

theorem generalDual3D_initialIdentification (W : PolynomialSatakeDualPair ι)
    (dlts μs : List ℂ) (hne : μs ≠ []) (s : ℂ)
    (hdlts : ∀ dlt ∈ dlts, 0 < (s + dlt).re) (hμ : ∀ μ ∈ μs, 0 < (s + μ).re)
    (hs : ((Fintype.card ι + W.dualExponent : ℕ) : ℝ) + 1 < s.re) :
    mellin (fun x : ℝ => generalDual3DTransformedReadout W dlts μs (1 / x)) s =
      generalDualCompletedReadout W dlts μs s := by
  have heq : mellin (fun x : ℝ => generalDual3DTransformedReadout W dlts μs (1 / x)) s =
      mellin (theta (cpsPolynomialDualCoeff W)
        (generalKernelLog dlts μs)) s := by
    unfold mellin
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    have hxpos : 0 < x := Set.mem_Ioi.mp hx
    dsimp only
    rw [generalDual3DTransformedReadout_eq_theta_one_div W dlts μs
      (one_div_pos.mpr hxpos)]
    simp
  rw [heq]
  let A : ℝ := (Fintype.card ι + W.dualExponent : ℕ)
  have ha : ∀ n : ℕ, ‖cpsPolynomialDualCoeff W n‖ ≤
      (1 : ℝ) * (((n + 1 : ℕ) : ℝ) ^ A) := by
    intro n
    change ‖cpsPolynomialDualCoeff W n‖ ≤
      1 * (((n + 1 : ℕ) : ℝ) ^
        ((Fintype.card ι + W.dualExponent : ℕ) : ℝ))
    rw [one_mul, Real.rpow_natCast]
    exact cpsPolynomialDualCoeff_norm_le W n
  have hg := generalKernelLog_hasMellin dlts μs hne s hdlts hμ
  have h := theta_hasMellin_of_polynomial
    (cpsPolynomialDualCoeff W) (generalKernelLog dlts μs)
      s 1 A hg.1 ha (by simpa [A] using hs)
  rw [h.2, hg.2]
  unfold generalDualCompletedReadout
  ring

end CriticalLinePhasor.GlobalHelix

#print axioms CriticalLinePhasor.GlobalHelix.generalKernelLog_nil
#print axioms CriticalLinePhasor.GlobalHelix.generalKernelLog_singleton
#print axioms CriticalLinePhasor.GlobalHelix.generalPrimal3DBankReadout_nil
#print axioms CriticalLinePhasor.GlobalHelix.generalPrimal3DBankReadout_singleton
#print axioms CriticalLinePhasor.GlobalHelix.weightedGeneralKernelLog_bounded
#print axioms CriticalLinePhasor.GlobalHelix.generalKernelLog_rapid
#print axioms CriticalLinePhasor.GlobalHelix.generalKernelLog_hasMellin
#print axioms CriticalLinePhasor.GlobalHelix.generalPrimal3DBankReadout_locallyIntegrableOn
#print axioms CriticalLinePhasor.GlobalHelix.generalDual3DReflectedReadout_locallyIntegrableOn
#print axioms CriticalLinePhasor.GlobalHelix.generalPrimal3DBankReadout_rapid
#print axioms CriticalLinePhasor.GlobalHelix.generalDual3DReflectedReadout_rapid
#print axioms CriticalLinePhasor.GlobalHelix.generalPrimal3D_initialIdentification
#print axioms CriticalLinePhasor.GlobalHelix.generalDual3D_initialIdentification
