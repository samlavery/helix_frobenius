import RequestProject.GlobalHelixCPSFullCompletion

/-!
# The real archimedean clock and the mixed completion kernel

The complex-place clock `gammaClock` (Mellin multiplier `Γℂ(s+μ)`) has carried every
completion kernel so far.  This file adds the **real place**:

* `gammaRClock` — the Gaussian clock `2·x^δ·e^{−πx²}` whose Mellin transform is exactly
  Deligne's real factor `Γℝ(s+δ)` (`gammaRClock_mellin`), with its convergence half-plane
  (`gammaRClock_mellinConvergent`) and signed-log weighted profile bound
  (`weightedGammaRLogProfile_norm_eq`, `weightedGammaRLogProfile_bounded`);
* `mixedKernelLog` — one real clock convolved in signed-log height with the complex-pair
  completion kernel; uniformly bounded at every admissible weight
  (`weightedMixedKernelLog_bounded`), rapidly decreasing (`mixedKernelLog_rapid`), with
  Mellin multiplier exactly `Γℝ(s+δ)·∏ Γℂ(s+μᵢ)` (`mixedKernelLog_hasMellin`) — the
  archimedean chart of every even symmetric power;
* `mixedPrimal3DBankReadout` / `mixedDual3DTransformedReadout` — the primal and
  reciprocal-height contragredient 3D banks carrying the mixed kernel, equal to
  coefficient theta functions on the positive carrier (`…_eq_theta`), locally integrable
  (`…_locallyIntegrableOn`) and rapidly decreasing (`…_rapid`) with all inputs compiled;
* `mixedPrimal3D_initialIdentification` / `mixedDual3D_initialIdentification` — on the
  initial half-plane the Mellin transforms of both banks are the completed readouts
  `Γℝ(s+δ)·∏ Γℂ(s+μᵢ)·D(s)`.

Everything is proven for every `PolynomialSatakeDualPair`, every real shift, and every
finite complex shift list.  No `axiom`, no `sorry`.
-/

open Finset ArithmeticFunction Complex UpperHalfPlane

namespace CriticalLinePhasor.GlobalHelix

open CriticalLinePhasor.CarrierTheta ConeProjection
open Set Filter Topology MeasureTheory Asymptotics


/-- The real-place archimedean clock: the Gaussian at shift `dlt`. -/
noncomputable def gammaRClock (dlt : ℂ) (x : ℝ) : ℂ :=
  2 * (x : ℂ) ^ dlt * Complex.exp (-(Real.pi : ℂ) * x ^ 2)

/-- Mellin convergence of the real clock in its half-plane. -/
theorem gammaRClock_mellinConvergent (dlt s : ℂ) (hs : 0 < (s + dlt).re) :
    MellinConvergent (gammaRClock dlt) s := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hbase : MellinConvergent (fun t : ℝ => (Real.exp (-t) : ℂ)) ((s + dlt) / 2) := by
    rw [MellinConvergent]
    simpa [smul_eq_mul, mul_comm] using
      (Complex.GammaIntegral_convergent (by
        rw [show ((s + dlt) / 2).re = (s + dlt).re / 2 by
          rw [Complex.div_re]
          simp [Complex.normSq]
          ring]
        positivity))
  have hscaled : MellinConvergent (fun t : ℝ => (Real.exp (-(Real.pi * t)) : ℂ))
      ((s + dlt) / 2) := by
    simpa only using ((MellinConvergent.comp_mul_left hπ).2 hbase)
  have hsq : MellinConvergent (fun t : ℝ => (Real.exp (-(Real.pi * t ^ (2:ℝ))) : ℂ))
      (s + dlt) := by
    have h := (MellinConvergent.comp_rpow (f := fun t : ℝ =>
      (Real.exp (-(Real.pi * t)) : ℂ)) (a := (2:ℝ)) (by norm_num)).2 hscaled
    simpa using h
  have hpow : MellinConvergent
      (fun t : ℝ => (t : ℂ) ^ dlt * (Real.exp (-(Real.pi * t ^ (2:ℝ))) : ℂ)) s :=
    (MellinConvergent.cpow_smul (E := ℂ)).2 hsq
  have hconst := hpow.const_smul (2 : ℂ)
  unfold gammaRClock
  refine hconst.congr_fun ?_ measurableSet_Ioi
  intro t ht
  have ht0 : (0:ℝ) < t := ht
  simp only [smul_eq_mul]
  rw [Complex.ofReal_exp]
  have hsq2 : t ^ (2:ℝ) = t ^ 2 := by
    rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  rw [show ((-(Real.pi * t ^ (2:ℝ)) : ℝ) : ℂ) = -(Real.pi : ℂ) * (t:ℂ) ^ 2 by
    rw [hsq2]; push_cast; ring]
  ring
/-- The Mellin transform of the real clock is the real-place Deligne factor:
`∫ t^{s-1}·2 t^{dlt} e^{-π t²} dt = Γℝ(s+dlt)`. -/
theorem gammaRClock_mellin (dlt s : ℂ) (hs : 0 < (s + dlt).re) :
    mellin (gammaRClock dlt) s = Complex.Gammaℝ (s + dlt) := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hre : 0 < ((s + dlt) / 2).re := by
    rw [show ((s + dlt) / 2).re = (s + dlt).re / 2 by
      rw [Complex.div_re]
      simp [Complex.normSq]
      ring]
    positivity
  unfold mellin gammaRClock
  simp only [smul_eq_mul]
  have hint :
      (∫ t : ℝ in Ioi 0,
        (t : ℂ) ^ (s - 1) * (2 * (t : ℂ) ^ dlt * Complex.exp (-(Real.pi : ℂ) * (t : ℂ) ^ 2)))
      = ∫ t : ℝ in Ioi 0, (|(2:ℝ)| * t ^ ((2:ℝ) - 1)) •
          ((fun u : ℝ => ((u : ℂ) ^ ((s + dlt) / 2 - 1) *
            Complex.exp (-((Real.pi : ℂ) * (u : ℂ))))) (t ^ (2:ℝ))) := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    have ht0 : (0:ℝ) < t := ht
    have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ht0)
    dsimp only
    rw [← cpow_mul_ofReal_nonneg ht0.le]
    rw [show ((2:ℝ) - 1) = 1 by norm_num, Real.rpow_one,
      show |(2:ℝ)| = 2 by norm_num]
    rw [show t ^ (2:ℝ) = t ^ 2 by
      rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]]
    rw [Complex.real_smul]
    rw [show (((2:ℝ) : ℂ) * ((s + dlt) / 2 - 1)) = s + dlt - 2 by push_cast; ring]
    rw [show ((t ^ 2 : ℝ) : ℂ) = (t : ℂ) ^ 2 by push_cast; ring]
    rw [show (t : ℂ) ^ (s - 1) * (2 * (t : ℂ) ^ dlt *
          Complex.exp (-(Real.pi : ℂ) * (t : ℂ) ^ 2))
        = 2 * ((t : ℂ) ^ (s - 1) * (t : ℂ) ^ dlt) *
          Complex.exp (-(Real.pi : ℂ) * (t : ℂ) ^ 2) by ring]
    rw [← Complex.cpow_add _ _ htc]
    rw [show ((2 * t : ℝ) : ℂ) * ((t : ℂ) ^ (s + dlt - 2) *
          Complex.exp (-((Real.pi : ℂ) * (t : ℂ) ^ 2)))
        = 2 * ((t : ℂ) * (t : ℂ) ^ (s + dlt - 2)) *
          Complex.exp (-((Real.pi : ℂ) * (t : ℂ) ^ 2)) by push_cast; ring]
    rw [show (t : ℂ) * (t : ℂ) ^ (s + dlt - 2) = (t : ℂ) ^ (s + dlt - 1) by
      rw [show s + dlt - 1 = 1 + (s + dlt - 2) by ring, Complex.cpow_add _ _ htc,
        Complex.cpow_one]]
    rw [show s - 1 + dlt = s + dlt - 1 by ring]
    ring
  rw [hint, MeasureTheory.integral_comp_rpow_Ioi
    (fun u : ℝ => ((u : ℂ) ^ ((s + dlt) / 2 - 1) *
      Complex.exp (-((Real.pi : ℂ) * (u : ℂ))))) (two_ne_zero (α := ℝ))]
  rw [show (∫ u : ℝ in Ioi 0, ((u : ℂ) ^ ((s + dlt) / 2 - 1) *
        Complex.exp (-((Real.pi : ℂ) * (u : ℂ)))))
      = (1 / (Real.pi : ℝ) : ℂ) ^ ((s + dlt) / 2) * Complex.Gamma ((s + dlt) / 2) from
    Complex.integral_cpow_mul_exp_neg_mul_Ioi hre hπ]
  rw [Complex.Gammaℝ_def]
  have hpow : ((1 / (Real.pi : ℝ) : ℂ)) ^ ((s + dlt) / 2)
      = ((Real.pi : ℝ) : ℂ) ^ (-(s + dlt) / 2) := by
    rw [one_div, Complex.inv_cpow _ _ (by
      rw [Complex.arg_ofReal_of_nonneg hπ.le]
      exact ne_of_lt Real.pi_pos), ← Complex.cpow_neg, neg_div]
  rw [hpow]

/-- Signed-log weighted norm of the real clock. -/
theorem weightedGammaRLogProfile_norm_eq (dlt : ℂ) (s u : ℝ) :
    ‖Complex.exp (-(s : ℂ) * u) * gammaRClock dlt (Real.exp (-u))‖ =
      2 * (Real.exp (-u)) ^ (s + dlt.re) *
        Real.exp (-Real.pi * (Real.exp (-u)) ^ (2:ℕ)) := by
  have ht : 0 < Real.exp (-u) := Real.exp_pos _
  rw [norm_mul, Complex.norm_exp, gammaRClock, norm_mul, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.norm_exp]
  norm_num
  have hcexp : ((Complex.exp (-(u : ℂ))) ^ 2).re = Real.exp (-u) ^ (2:ℕ) := by
    rw [show -(u : ℂ) = ((-u : ℝ) : ℂ) by push_cast; rfl, ← Complex.ofReal_exp,
      ← Complex.ofReal_pow, Complex.ofReal_re]
  rw [hcexp]
  have hsPow : Real.exp (-(s * u)) = (Real.exp (-u)) ^ s := by
    rw [Real.rpow_def_of_pos ht, Real.log_exp]
    congr 1
    ring
  rw [hsPow]
  calc
    Real.exp (-u) ^ s *
        (2 * Real.exp (-u) ^ dlt.re * Real.exp (-(Real.pi * Real.exp (-u) ^ (2:ℕ)))) =
        2 * (Real.exp (-u) ^ s * Real.exp (-u) ^ dlt.re) *
          Real.exp (-(Real.pi * Real.exp (-u) ^ (2:ℕ))) := by ring
    _ = 2 * Real.exp (-u) ^ (s + dlt.re) *
          Real.exp (-(Real.pi * Real.exp (-u) ^ (2:ℕ))) := by
      rw [Real.rpow_add ht]

/-- Every sufficiently positive real Mellin weight makes the real clock uniformly bounded in
signed-log height. -/
theorem weightedGammaRLogProfile_bounded (dlt : ℂ) (s : ℝ) (hs : 0 < s + dlt.re) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ u : ℝ,
      ‖Complex.exp (-(s : ℂ) * u) * gammaRClock dlt (Real.exp (-u))‖ ≤ B := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  refine ⟨2 * max 1 (Real.exp ((s + dlt.re) *
      (Real.log ((s + dlt.re) / Real.pi) - 1))), by positivity, ?_⟩
  intro u
  rw [weightedGammaRLogProfile_norm_eq]
  set y : ℝ := Real.exp (-u) with hy
  have hy0 : 0 < y := Real.exp_pos _
  by_cases hy1 : y ≤ 1
  · calc
      2 * y ^ (s + dlt.re) * Real.exp (-Real.pi * y ^ (2:ℕ)) ≤ 2 * 1 * 1 := by
        apply mul_le_mul
        · apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact Real.rpow_le_one hy0.le hy1 hs.le
        · exact Real.exp_le_one_iff.mpr (by nlinarith)
        · positivity
        · norm_num
      _ ≤ 2 * max 1 (Real.exp ((s + dlt.re) *
            (Real.log ((s + dlt.re) / Real.pi) - 1))) := by
        rw [mul_one]
        exact mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num)
  · rw [not_le] at hy1
    have hsq : y ≤ y ^ (2:ℕ) := by nlinarith
    calc
      2 * y ^ (s + dlt.re) * Real.exp (-Real.pi * y ^ (2:ℕ))
          ≤ 2 * (y ^ (s + dlt.re) * Real.exp (-Real.pi * y)) := by
        rw [mul_assoc]
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hy0.le _)
        exact Real.exp_le_exp.mpr (by nlinarith)
      _ ≤ 2 * Real.exp ((s + dlt.re) *
            (Real.log ((s + dlt.re) / Real.pi) - 1)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact rpow_mul_exp_neg_le_exp_log_ratio hs hπ hy0
      _ ≤ 2 * max 1 (Real.exp ((s + dlt.re) *
            (Real.log ((s + dlt.re) / Real.pi) - 1))) :=
        mul_le_mul_of_nonneg_left (le_max_right _ _) (by norm_num)

/-- The mixed archimedean kernel: one real clock convolved (in signed-log height) with the
complex-pair completion kernel. -/
noncomputable def mixedKernelLog (dlt : ℂ) (μs : List ℂ) : ℝ → ℂ :=
  logMellinConvolution (gammaRClock dlt) (completionKernelLog μs)

/-- A common sufficiently positive real Mellin weight makes the mixed kernel uniformly bounded. -/
theorem weightedMixedKernelLog_bounded
    (dlt : ℂ) (μs : List ℂ) (hne : μs ≠ []) (s : ℝ)
    (hdlt : 0 < s + dlt.re) (hs : ∀ μ ∈ μs, 0 < s + μ.re) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ u : ℝ,
      ‖Complex.exp (-(s : ℂ) * u) *
        mixedKernelLog dlt μs (Real.exp (-u))‖ ≤ B := by
  obtain ⟨B, hB, hbound⟩ := weightedCompletionKernelLog_bounded μs hne s hs
  let F : ℝ → ℂ := fun u =>
    Complex.exp (-(s : ℂ) * u) * gammaRClock dlt (Real.exp (-u))
  let G : ℝ → ℂ := fun u =>
    Complex.exp (-(s : ℂ) * u) * completionKernelLog μs (Real.exp (-u))
  have hsdlt : 0 < (((s : ℝ) : ℂ) + dlt).re := by simpa using hdlt
  have hF : Integrable F :=
    (mellinConvergent_iff_negLogIntegrable (gammaRClock dlt) (s : ℂ)).mp
      (gammaRClock_mellinConvergent dlt (s : ℂ) hsdlt)
  refine ⟨B * ∫ u : ℝ, ‖F u‖,
    mul_nonneg hB (integral_nonneg fun _ => norm_nonneg _), ?_⟩
  intro u
  rw [show mixedKernelLog dlt μs =
      logMellinConvolution (gammaRClock dlt) (completionKernelLog μs) by rfl,
    weighted_logMellinConvolution_eq_convolution]
  exact norm_convolution_mul_le_of_integrable_of_bound F G hF B hbound u

/-- The mixed kernel decreases faster than every real power at positive infinity. -/
theorem mixedKernelLog_rapid (dlt : ℂ) (μs : List ℂ) (hne : μs ≠ []) :
    ∀ q : ℝ, mixedKernelLog dlt μs =O[atTop] (fun x : ℝ => x ^ q) := by
  intro q
  obtain ⟨s, hsq, hs⟩ := exists_weight_gt_neg_and_shifts q (dlt :: μs)
  have hdlt : 0 < s + dlt.re := by linarith [hs dlt (by simp)]
  have hspos : ∀ μ ∈ μs, 0 < s + μ.re := by
    intro μ hμ
    linarith [hs μ (by simp [hμ])]
  obtain ⟨B, hB, hbound⟩ :=
    weightedMixedKernelLog_bounded dlt μs hne s hdlt hspos
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
  have hraw' : ‖mixedKernelLog dlt μs x‖ * x ^ s ≤ B := by
    simpa [mul_comm] using hraw
  have hpow : 0 < x ^ s := Real.rpow_pos_of_pos hx s
  have hk : ‖mixedKernelLog dlt μs x‖ ≤ B * x ^ (-s) := by
    have hdiv := (le_div_iff₀ hpow).2 hraw'
    rwa [div_eq_mul_inv, ← Real.rpow_neg hx.le] at hdiv
  calc
    ‖mixedKernelLog dlt μs x‖ ≤ B * x ^ (-s) := hk
    _ ≤ (B + 1) * x ^ (-s) := by gcongr; linarith
    _ ≤ (B + 1) * x ^ q := by
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith : -s ≤ q))
        (by linarith)
    _ = (B + 1) * ‖x ^ q‖ := by
      rw [Real.norm_of_nonneg (Real.rpow_nonneg hx.le q)]

/-- The mixed kernel has exactly the mixed Deligne multiplier `Γℝ(s+dlt)·∏ Γℂ(s+μ)`. -/
theorem mixedKernelLog_hasMellin
    (dlt : ℂ) (μs : List ℂ) (hne : μs ≠ []) (s : ℂ)
    (hdlt : 0 < (s + dlt).re) (hs : ∀ μ ∈ μs, 0 < (s + μ).re) :
    HasMellin (mixedKernelLog dlt μs) s
      (Complex.Gammaℝ (s + dlt) *
        (μs.map fun μ => Complex.Gammaℂ (s + μ)).prod) := by
  have hR : HasMellin (gammaRClock dlt) s (Complex.Gammaℝ (s + dlt)) :=
    ⟨gammaRClock_mellinConvergent dlt s hdlt, gammaRClock_mellin dlt s hdlt⟩
  have hC := completionKernelLog_hasMellin μs hne s hs
  have hconv := logMellinConvolution_hasMellin
    (gammaRClock dlt) (completionKernelLog μs) s hR.1 hC.1
  rw [show mixedKernelLog dlt μs =
      logMellinConvolution (gammaRClock dlt) (completionKernelLog μs) from rfl]
  exact ⟨hconv.1, by rw [hconv.2, hR.2, hC.2]⟩

variable {ι : Type*} [Fintype ι]

/-- The primal 3D bank carrying the mixed real/complex archimedean kernel. -/
noncomputable def mixedPrimal3DBankReadout (W : PolynomialSatakeDualPair ι)
    (dlt : ℂ) (μs : List ℂ) (x : ℝ) : ℂ :=
  ∑' n : ℕ,
    fiberPhasor (coefficientFiber (cpsPolynomialPrimalCoeff W) n x) *
      mixedKernelLog dlt μs
        (multiplicativeHeight (coefficientFiber (cpsPolynomialPrimalCoeff W) n x))

/-- The reciprocal-height contragredient 3D bank with the mixed kernel. -/
noncomputable def mixedDual3DTransformedReadout (W : PolynomialSatakeDualPair ι)
    (dlt : ℂ) (μs : List ℂ) (x : ℝ) : ℂ :=
  ∑' n : ℕ,
    fiberPhasor
        (reciprocalCoefficientFiber
          (fun j => (starRingEnd ℂ) (cpsPolynomialDualCoeff W j)) n x) *
      mixedKernelLog dlt μs
        (multiplicativeHeight
          (reciprocalCoefficientFiber
            (fun j => (starRingEnd ℂ) (cpsPolynomialDualCoeff W j)) n x))

theorem mixedPrimal3DBankReadout_eq_theta (W : PolynomialSatakeDualPair ι)
    (dlt : ℂ) (μs : List ℂ) {x : ℝ} (hx : 0 < x) :
    mixedPrimal3DBankReadout W dlt μs x =
      theta (cpsPolynomialPrimalCoeff W) (mixedKernelLog dlt μs) x := by
  unfold mixedPrimal3DBankReadout theta
  apply tsum_congr
  intro n
  rw [fiberPhasor_coefficientFiber,
    multiplicativeHeight_coefficientFiber (cpsPolynomialPrimalCoeff W) n hx]

theorem mixedDual3DTransformedReadout_eq_theta_one_div (W : PolynomialSatakeDualPair ι)
    (dlt : ℂ) (μs : List ℂ) {x : ℝ} (hx : 0 < x) :
    mixedDual3DTransformedReadout W dlt μs x =
      theta (cpsPolynomialDualCoeff W) (mixedKernelLog dlt μs) (1 / x) := by
  unfold mixedDual3DTransformedReadout theta
  apply tsum_congr
  intro n
  rw [fiberPhasor_reciprocalCoefficientFiber_conj,
    multiplicativeHeight_reciprocalCoefficientFiber _ n hx]
  simp [div_eq_mul_inv]

/-- One admissible common Mellin weight for the mixed chart and both coefficient banks. -/
theorem exists_mixed_weight (q : ℝ) (dlt : ℂ) (μs : List ℂ) :
    ∃ σ : ℝ, -q < σ ∧ 0 < σ + dlt.re ∧ ∀ μ ∈ μs, 0 < σ + μ.re := by
  obtain ⟨σ, hσq, hσ⟩ := exists_weight_gt_neg_and_shifts q (dlt :: μs)
  exact ⟨σ, hσq, by linarith [hσ dlt (by simp)],
    fun μ hμ => by linarith [hσ μ (by simp [hμ])]⟩

theorem mixedPrimalTheta_locallyIntegrableOn (W : PolynomialSatakeDualPair ι)
    (dlt : ℂ) (μs : List ℂ) (hne : μs ≠ []) :
    MeasureTheory.LocallyIntegrableOn
      (theta (cpsPolynomialPrimalCoeff W) (mixedKernelLog dlt μs))
      (Set.Ioi 0) := by
  let A : ℝ := (Fintype.card ι + W.primalExponent : ℕ)
  obtain ⟨σ, hσA, hσdlt, hσμ⟩ := exists_mixed_weight (-(A + 1)) dlt μs
  have hA : A + 1 < ((σ : ℂ).re) := by simpa using hσA
  have hdlt : 0 < (((σ : ℂ) + dlt).re) := by
    simp only [Complex.add_re, Complex.ofReal_re]
    exact hσdlt
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
  have hg := mixedKernelLog_hasMellin dlt μs hne (σ : ℂ) hdlt hμ
  have htheta := theta_hasMellin_of_polynomial
    (cpsPolynomialPrimalCoeff W) (mixedKernelLog dlt μs)
      (σ : ℂ) 1 A hg.1 ha hA
  exact locallyIntegrableOn_of_mellinConvergent _ _ htheta.1

theorem mixedDualTheta_locallyIntegrableOn (W : PolynomialSatakeDualPair ι)
    (dlt : ℂ) (μs : List ℂ) (hne : μs ≠ []) :
    MeasureTheory.LocallyIntegrableOn
      (theta (cpsPolynomialDualCoeff W) (mixedKernelLog dlt μs))
      (Set.Ioi 0) := by
  let A : ℝ := (Fintype.card ι + W.dualExponent : ℕ)
  obtain ⟨σ, hσA, hσdlt, hσμ⟩ := exists_mixed_weight (-(A + 1)) dlt μs
  have hA : A + 1 < ((σ : ℂ).re) := by simpa using hσA
  have hdlt : 0 < (((σ : ℂ) + dlt).re) := by
    simp only [Complex.add_re, Complex.ofReal_re]
    exact hσdlt
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
  have hg := mixedKernelLog_hasMellin dlt μs hne (σ : ℂ) hdlt hμ
  have htheta := theta_hasMellin_of_polynomial
    (cpsPolynomialDualCoeff W) (mixedKernelLog dlt μs)
      (σ : ℂ) 1 A hg.1 ha hA
  exact locallyIntegrableOn_of_mellinConvergent _ _ htheta.1

theorem mixedPrimal3DBankReadout_locallyIntegrableOn (W : PolynomialSatakeDualPair ι)
    (dlt : ℂ) (μs : List ℂ) (hne : μs ≠ []) :
    MeasureTheory.LocallyIntegrableOn (mixedPrimal3DBankReadout W dlt μs) (Set.Ioi 0) := by
  apply MeasureTheory.LocallyIntegrableOn.congr _
    (mixedPrimalTheta_locallyIntegrableOn W dlt μs hne)
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
  exact (mixedPrimal3DBankReadout_eq_theta W dlt μs hx).symm

theorem mixedDual3DReflectedReadout_locallyIntegrableOn (W : PolynomialSatakeDualPair ι)
    (dlt : ℂ) (μs : List ℂ) (hne : μs ≠ []) :
    MeasureTheory.LocallyIntegrableOn
      (fun x : ℝ => mixedDual3DTransformedReadout W dlt μs (1 / x)) (Set.Ioi 0) := by
  apply MeasureTheory.LocallyIntegrableOn.congr _
    (mixedDualTheta_locallyIntegrableOn W dlt μs hne)
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
  have hxpos : 0 < x := Set.mem_Ioi.mp hx
  rw [mixedDual3DTransformedReadout_eq_theta_one_div W dlt μs
    (one_div_pos.mpr hxpos)]
  simp

theorem mixedPrimal3DBankReadout_rapid (W : PolynomialSatakeDualPair ι)
    (dlt : ℂ) (μs : List ℂ) (hne : μs ≠ []) :
    ∀ q : ℝ, mixedPrimal3DBankReadout W dlt μs =O[atTop] (fun x : ℝ => x ^ q) := by
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
    (cpsPolynomialPrimalCoeff W) (mixedKernelLog dlt μs)
      1 A zero_le_one ha (mixedKernelLog_rapid dlt μs hne)
  intro q
  have heq :
      theta (cpsPolynomialPrimalCoeff W)
          (mixedKernelLog dlt μs) =ᶠ[atTop]
        mixedPrimal3DBankReadout W dlt μs := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact (mixedPrimal3DBankReadout_eq_theta W dlt μs hx).symm
  simpa using (htheta q).congr' heq Filter.EventuallyEq.rfl

theorem mixedDual3DReflectedReadout_rapid (W : PolynomialSatakeDualPair ι)
    (dlt : ℂ) (μs : List ℂ) (hne : μs ≠ []) :
    ∀ q : ℝ,
      (fun x : ℝ => mixedDual3DTransformedReadout W dlt μs (1 / x))
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
    (cpsPolynomialDualCoeff W) (mixedKernelLog dlt μs)
      1 A zero_le_one ha (mixedKernelLog_rapid dlt μs hne)
  intro q
  have heq :
      theta (cpsPolynomialDualCoeff W)
          (mixedKernelLog dlt μs) =ᶠ[atTop]
        (fun x : ℝ => mixedDual3DTransformedReadout W dlt μs (1 / x)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [mixedDual3DTransformedReadout_eq_theta_one_div W dlt μs
      (one_div_pos.mpr hx)]
    simp
  simpa using (htheta q).congr' heq Filter.EventuallyEq.rfl

/-- The mixed completed readout: real factor, complex factors, Dirichlet readout. -/
noncomputable def mixedPrimalCompletedReadout (W : PolynomialSatakeDualPair ι)
    (dlt : ℂ) (μs : List ℂ) (s : ℂ) : ℂ :=
  Complex.Gammaℝ (s + dlt) * (μs.map fun μ => Complex.Gammaℂ (s + μ)).prod *
    dirichlet (cpsPolynomialPrimalCoeff W) s

noncomputable def mixedDualCompletedReadout (W : PolynomialSatakeDualPair ι)
    (dlt : ℂ) (μs : List ℂ) (s : ℂ) : ℂ :=
  Complex.Gammaℝ (s + dlt) * (μs.map fun μ => Complex.Gammaℂ (s + μ)).prod *
    dirichlet (cpsPolynomialDualCoeff W) s

theorem mixedPrimal3D_initialIdentification (W : PolynomialSatakeDualPair ι)
    (dlt : ℂ) (μs : List ℂ) (hne : μs ≠ []) (s : ℂ)
    (hdlt : 0 < (s + dlt).re) (hμ : ∀ μ ∈ μs, 0 < (s + μ).re)
    (hs : ((Fintype.card ι + W.primalExponent : ℕ) : ℝ) + 1 < s.re) :
    mellin (mixedPrimal3DBankReadout W dlt μs) s =
      mixedPrimalCompletedReadout W dlt μs s := by
  have heq : mellin (mixedPrimal3DBankReadout W dlt μs) s =
      mellin (theta (cpsPolynomialPrimalCoeff W)
        (mixedKernelLog dlt μs)) s := by
    unfold mellin
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp only
    rw [mixedPrimal3DBankReadout_eq_theta W dlt μs (Set.mem_Ioi.mp hx)]
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
  have hg := mixedKernelLog_hasMellin dlt μs hne s hdlt hμ
  have h := theta_hasMellin_of_polynomial
    (cpsPolynomialPrimalCoeff W) (mixedKernelLog dlt μs)
      s 1 A hg.1 ha (by simpa [A] using hs)
  rw [h.2, hg.2]
  unfold mixedPrimalCompletedReadout
  ring

theorem mixedDual3D_initialIdentification (W : PolynomialSatakeDualPair ι)
    (dlt : ℂ) (μs : List ℂ) (hne : μs ≠ []) (s : ℂ)
    (hdlt : 0 < (s + dlt).re) (hμ : ∀ μ ∈ μs, 0 < (s + μ).re)
    (hs : ((Fintype.card ι + W.dualExponent : ℕ) : ℝ) + 1 < s.re) :
    mellin (fun x : ℝ => mixedDual3DTransformedReadout W dlt μs (1 / x)) s =
      mixedDualCompletedReadout W dlt μs s := by
  have heq : mellin (fun x : ℝ => mixedDual3DTransformedReadout W dlt μs (1 / x)) s =
      mellin (theta (cpsPolynomialDualCoeff W)
        (mixedKernelLog dlt μs)) s := by
    unfold mellin
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    have hxpos : 0 < x := Set.mem_Ioi.mp hx
    dsimp only
    rw [mixedDual3DTransformedReadout_eq_theta_one_div W dlt μs
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
  have hg := mixedKernelLog_hasMellin dlt μs hne s hdlt hμ
  have h := theta_hasMellin_of_polynomial
    (cpsPolynomialDualCoeff W) (mixedKernelLog dlt μs)
      s 1 A hg.1 ha (by simpa [A] using hs)
  rw [h.2, hg.2]
  unfold mixedDualCompletedReadout
  ring

end CriticalLinePhasor.GlobalHelix

#print axioms CriticalLinePhasor.GlobalHelix.gammaRClock_mellinConvergent
#print axioms CriticalLinePhasor.GlobalHelix.gammaRClock_mellin
#print axioms CriticalLinePhasor.GlobalHelix.weightedGammaRLogProfile_bounded
#print axioms CriticalLinePhasor.GlobalHelix.weightedMixedKernelLog_bounded
#print axioms CriticalLinePhasor.GlobalHelix.mixedKernelLog_rapid
#print axioms CriticalLinePhasor.GlobalHelix.mixedKernelLog_hasMellin
#print axioms CriticalLinePhasor.GlobalHelix.mixedPrimal3DBankReadout_locallyIntegrableOn
#print axioms CriticalLinePhasor.GlobalHelix.mixedDual3DReflectedReadout_locallyIntegrableOn
#print axioms CriticalLinePhasor.GlobalHelix.mixedPrimal3DBankReadout_rapid
#print axioms CriticalLinePhasor.GlobalHelix.mixedDual3DReflectedReadout_rapid
#print axioms CriticalLinePhasor.GlobalHelix.mixedPrimal3D_initialIdentification
#print axioms CriticalLinePhasor.GlobalHelix.mixedDual3D_initialIdentification
