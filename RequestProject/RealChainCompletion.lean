import RequestProject.GeneralSeed

/-!
# The pure-real chain kernel: the Maass chart at every rank

The compiled kernel family covers `∏Γℝ·∏Γℂ` with nonempty complex part.  Maass charts
are pure-real — `Γℝ(s+it)Γℝ(s−it)` at the seed, `r+1` real clocks at `Sym^r` — so this
file adds the nonempty **real chain**: a head clock convolved with a list of real
clocks in signed-log height.

* `realChainKernelLog d ds` — head `Γℝ`-clock, then the chain; Mellin multiplier
  exactly `∏_{δ ∈ d::ds} Γℝ(s+δ)` (`realChainKernelLog_hasMellin`), uniformly bounded
  at every admissible weight (`weightedRealChainKernelLog_bounded`), rapidly
  decreasing (`realChainKernelLog_rapid`) — induction over the chain, base the
  compiled single real clock;
* the full 3D bank layer on this kernel (primal and contragredient readouts, theta
  identifications, local integrability, rapid decay, both initial-half-plane
  identifications);
* `RealNicePackage` (+ `unique`) and `mechanismRR` — **the mechanism at the pure-real
  chart**: one theta identity yields the complete package
  `Λ(s) = ∏Γℝ(s+δ)·L(s)`;
* `symr_real_package_of_theta_of` — the mechanism at every rank over every seed at
  pure-real charts: the Maass symmetric powers' chart type.

No `axiom`, no `sorry`.
-/

open Finset ArithmeticFunction Complex UpperHalfPlane

namespace CriticalLinePhasor.GlobalHelix

open CriticalLinePhasor.CarrierTheta ConeProjection
open Set Filter Topology MeasureTheory Asymptotics

/-- The pure-real chain kernel: a head real clock convolved with a list of real
clocks. -/
noncomputable def realChainKernelLog : ℂ → List ℂ → ℝ → ℂ
  | d, [] => gammaRClock d
  | d, e :: es => logMellinConvolution (gammaRClock d) (realChainKernelLog e es)

/-- A common sufficiently positive Mellin weight bounds the chain uniformly. -/
theorem weightedRealChainKernelLog_bounded (d : ℂ) (ds : List ℂ) (s : ℝ)
    (hd : 0 < s + d.re) (hds : ∀ e ∈ ds, 0 < s + e.re) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ u : ℝ,
      ‖Complex.exp (-(s : ℂ) * u) * realChainKernelLog d ds (Real.exp (-u))‖ ≤ B := by
  induction ds generalizing d with
  | nil => exact weightedGammaRLogProfile_bounded d s hd
  | cons e es ih =>
      obtain ⟨B, hB, hbound⟩ := ih e (hds e (by simp)) (fun z hz => hds z (by simp [hz]))
      let F : ℝ → ℂ := fun u =>
        Complex.exp (-(s : ℂ) * u) * gammaRClock d (Real.exp (-u))
      let G : ℝ → ℂ := fun u =>
        Complex.exp (-(s : ℂ) * u) * realChainKernelLog e es (Real.exp (-u))
      have hsd : 0 < (((s : ℝ) : ℂ) + d).re := by
        simpa using hd
      have hF : Integrable F :=
        (mellinConvergent_iff_negLogIntegrable (gammaRClock d) (s : ℂ)).mp
          (gammaRClock_mellinConvergent d (s : ℂ) hsd)
      refine ⟨B * ∫ u : ℝ, ‖F u‖,
        mul_nonneg hB (integral_nonneg fun _ => norm_nonneg _), ?_⟩
      intro u
      rw [show realChainKernelLog d (e :: es)
          = logMellinConvolution (gammaRClock d) (realChainKernelLog e es) from rfl,
        weighted_logMellinConvolution_eq_convolution]
      exact norm_convolution_mul_le_of_integrable_of_bound F G hF B hbound u

/-- The chain decreases faster than every real power at positive infinity. -/
theorem realChainKernelLog_rapid (d : ℂ) (ds : List ℂ) :
    ∀ q : ℝ, realChainKernelLog d ds =O[atTop] (fun x : ℝ => x ^ q) := by
  intro q
  obtain ⟨s, hsq, hall⟩ := exists_weight_gt_neg_and_shifts q (d :: ds)
  have hd : 0 < s + d.re := by linarith [hall d (by simp)]
  have hds : ∀ e ∈ ds, 0 < s + e.re := by
    intro z hz
    linarith [hall z (by simp [hz])]
  obtain ⟨B, hB, hbound⟩ := weightedRealChainKernelLog_bounded d ds s hd hds
  rw [Asymptotics.isBigO_iff']
  refine ⟨B + 1, by linarith, ?_⟩
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx1
  have hx : 0 < x := zero_lt_one.trans hx1
  have hweight :
      ‖Complex.exp (-(s : ℂ) * ((-Real.log x : ℝ) : ℂ))‖ = x ^ s := by
    rw [Complex.norm_exp]
    have : (-(s : ℂ) * ((-Real.log x : ℝ) : ℂ)).re = s * Real.log x := by
      norm_num
    rw [this, Real.rpow_def_of_pos hx]
    congr 1
    ring
  have hraw := hbound (-Real.log x)
  have hexp : Real.exp (-(-Real.log x)) = x := by
    rw [neg_neg, Real.exp_log hx]
  rw [hexp, norm_mul, hweight] at hraw
  have hraw' : ‖realChainKernelLog d ds x‖ * x ^ s ≤ B := by
    simpa [mul_comm] using hraw
  have hpow : 0 < x ^ s := Real.rpow_pos_of_pos hx s
  have hk : ‖realChainKernelLog d ds x‖ ≤ B * x ^ (-s) := by
    have hdiv := (le_div_iff₀ hpow).2 hraw'
    rwa [div_eq_mul_inv, ← Real.rpow_neg hx.le] at hdiv
  calc
    ‖realChainKernelLog d ds x‖ ≤ B * x ^ (-s) := hk
    _ ≤ (B + 1) * x ^ (-s) := by gcongr; linarith
    _ ≤ (B + 1) * x ^ q := by
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith : -s ≤ q))
        (by linarith)
    _ = (B + 1) * ‖x ^ q‖ := by
      rw [Real.norm_of_nonneg (Real.rpow_nonneg hx.le q)]

/-- **The chain has exactly the pure-real Deligne multiplier.** -/
theorem realChainKernelLog_hasMellin (d : ℂ) (ds : List ℂ) (s : ℂ)
    (hd : 0 < (s + d).re) (hds : ∀ e ∈ ds, 0 < (s + e).re) :
    HasMellin (realChainKernelLog d ds) s
      (((d :: ds).map fun e => Complex.Gammaℝ (s + e)).prod) := by
  induction ds generalizing d with
  | nil =>
      rw [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      exact ⟨gammaRClock_mellinConvergent d s hd, gammaRClock_mellin d s hd⟩
  | cons e es ih =>
      have hR : HasMellin (gammaRClock d) s (Complex.Gammaℝ (s + d)) :=
        ⟨gammaRClock_mellinConvergent d s hd, gammaRClock_mellin d s hd⟩
      have htail := ih e (hds e (by simp)) (fun z hz => hds z (by simp [hz]))
      have hconv := logMellinConvolution_hasMellin (gammaRClock d)
        (realChainKernelLog e es) s hR.1 htail.1
      rw [show realChainKernelLog d (e :: es)
          = logMellinConvolution (gammaRClock d) (realChainKernelLog e es) from rfl]
      refine ⟨hconv.1, ?_⟩
      rw [hconv.2, hR.2, htail.2]
      simp only [List.map_cons, List.prod_cons]


variable {ι : Type*} [Fintype ι]

/-- The primal 3D bank carrying the pure-real chain kernel. -/
noncomputable def realPrimal3DBankReadout (W : PolynomialSatakeDualPair ι)
    (d : ℂ) (ds : List ℂ) (x : ℝ) : ℂ :=
  ∑' n : ℕ,
    fiberPhasor (coefficientFiber (cpsPolynomialPrimalCoeff W) n x) *
      realChainKernelLog d ds
        (multiplicativeHeight (coefficientFiber (cpsPolynomialPrimalCoeff W) n x))

/-- The reciprocal-height contragredient 3D bank with the chain kernel. -/
noncomputable def realDual3DTransformedReadout (W : PolynomialSatakeDualPair ι)
    (d : ℂ) (ds : List ℂ) (x : ℝ) : ℂ :=
  ∑' n : ℕ,
    fiberPhasor
        (reciprocalCoefficientFiber
          (fun j => (starRingEnd ℂ) (cpsPolynomialDualCoeff W j)) n x) *
      realChainKernelLog d ds
        (multiplicativeHeight
          (reciprocalCoefficientFiber
            (fun j => (starRingEnd ℂ) (cpsPolynomialDualCoeff W j)) n x))

theorem realPrimal3DBankReadout_eq_theta (W : PolynomialSatakeDualPair ι)
    (d : ℂ) (ds : List ℂ) {x : ℝ} (hx : 0 < x) :
    realPrimal3DBankReadout W d ds x =
      CriticalLinePhasor.CarrierTheta.theta (cpsPolynomialPrimalCoeff W)
        (realChainKernelLog d ds) x := by
  unfold realPrimal3DBankReadout CriticalLinePhasor.CarrierTheta.theta
  apply tsum_congr
  intro n
  rw [fiberPhasor_coefficientFiber,
    multiplicativeHeight_coefficientFiber (cpsPolynomialPrimalCoeff W) n hx]

theorem realDual3DTransformedReadout_eq_theta_one_div (W : PolynomialSatakeDualPair ι)
    (d : ℂ) (ds : List ℂ) {x : ℝ} (hx : 0 < x) :
    realDual3DTransformedReadout W d ds x =
      CriticalLinePhasor.CarrierTheta.theta (cpsPolynomialDualCoeff W)
        (realChainKernelLog d ds) (1 / x) := by
  unfold realDual3DTransformedReadout CriticalLinePhasor.CarrierTheta.theta
  apply tsum_congr
  intro n
  rw [fiberPhasor_reciprocalCoefficientFiber_conj,
    multiplicativeHeight_reciprocalCoefficientFiber _ n hx]
  simp [div_eq_mul_inv]

theorem exists_realChain_weight (q : ℝ) (d : ℂ) (ds : List ℂ) :
    ∃ σ : ℝ, -q < σ ∧ 0 < σ + d.re ∧ ∀ e ∈ ds, 0 < σ + e.re := by
  obtain ⟨σ, hσq, hσ⟩ := exists_weight_gt_neg_and_shifts q (d :: ds)
  exact ⟨σ, hσq, by linarith [hσ d (by simp)],
    fun e he => by linarith [hσ e (by simp [he])]⟩

theorem realPrimalTheta_locallyIntegrableOn (W : PolynomialSatakeDualPair ι)
    (d : ℂ) (ds : List ℂ) :
    MeasureTheory.LocallyIntegrableOn
      (CriticalLinePhasor.CarrierTheta.theta (cpsPolynomialPrimalCoeff W)
        (realChainKernelLog d ds)) (Set.Ioi 0) := by
  let A : ℝ := (Fintype.card ι + W.primalExponent : ℕ)
  obtain ⟨σ, hσA, hσd, hσds⟩ := exists_realChain_weight (-(A + 1)) d ds
  have hA : A + 1 < ((σ : ℂ).re) := by simpa using hσA
  have hd : 0 < (((σ : ℂ) + d).re) := by
    simp only [Complex.add_re, Complex.ofReal_re]
    exact hσd
  have hds : ∀ e ∈ ds, 0 < (((σ : ℂ) + e).re) := by
    intro e he
    simp only [Complex.add_re, Complex.ofReal_re]
    exact hσds e he
  have ha : ∀ n : ℕ, ‖cpsPolynomialPrimalCoeff W n‖ ≤
      (1 : ℝ) * (((n + 1 : ℕ) : ℝ) ^ A) := by
    intro n
    change ‖cpsPolynomialPrimalCoeff W n‖ ≤
      1 * (((n + 1 : ℕ) : ℝ) ^
        ((Fintype.card ι + W.primalExponent : ℕ) : ℝ))
    rw [one_mul, Real.rpow_natCast]
    exact cpsPolynomialPrimalCoeff_norm_le W n
  have hg := realChainKernelLog_hasMellin d ds (σ : ℂ) hd hds
  have htheta := CriticalLinePhasor.CarrierTheta.theta_hasMellin_of_polynomial
    (cpsPolynomialPrimalCoeff W) (realChainKernelLog d ds)
      (σ : ℂ) 1 A hg.1 ha hA
  exact CriticalLinePhasor.CarrierTheta.locallyIntegrableOn_of_mellinConvergent _ _ htheta.1

theorem realDualTheta_locallyIntegrableOn (W : PolynomialSatakeDualPair ι)
    (d : ℂ) (ds : List ℂ) :
    MeasureTheory.LocallyIntegrableOn
      (CriticalLinePhasor.CarrierTheta.theta (cpsPolynomialDualCoeff W)
        (realChainKernelLog d ds)) (Set.Ioi 0) := by
  let A : ℝ := (Fintype.card ι + W.dualExponent : ℕ)
  obtain ⟨σ, hσA, hσd, hσds⟩ := exists_realChain_weight (-(A + 1)) d ds
  have hA : A + 1 < ((σ : ℂ).re) := by simpa using hσA
  have hd : 0 < (((σ : ℂ) + d).re) := by
    simp only [Complex.add_re, Complex.ofReal_re]
    exact hσd
  have hds : ∀ e ∈ ds, 0 < (((σ : ℂ) + e).re) := by
    intro e he
    simp only [Complex.add_re, Complex.ofReal_re]
    exact hσds e he
  have ha : ∀ n : ℕ, ‖cpsPolynomialDualCoeff W n‖ ≤
      (1 : ℝ) * (((n + 1 : ℕ) : ℝ) ^ A) := by
    intro n
    change ‖cpsPolynomialDualCoeff W n‖ ≤
      1 * (((n + 1 : ℕ) : ℝ) ^
        ((Fintype.card ι + W.dualExponent : ℕ) : ℝ))
    rw [one_mul, Real.rpow_natCast]
    exact cpsPolynomialDualCoeff_norm_le W n
  have hg := realChainKernelLog_hasMellin d ds (σ : ℂ) hd hds
  have htheta := CriticalLinePhasor.CarrierTheta.theta_hasMellin_of_polynomial
    (cpsPolynomialDualCoeff W) (realChainKernelLog d ds)
      (σ : ℂ) 1 A hg.1 ha hA
  exact CriticalLinePhasor.CarrierTheta.locallyIntegrableOn_of_mellinConvergent _ _ htheta.1

theorem realPrimal3DBankReadout_locallyIntegrableOn (W : PolynomialSatakeDualPair ι)
    (d : ℂ) (ds : List ℂ) :
    MeasureTheory.LocallyIntegrableOn (realPrimal3DBankReadout W d ds) (Set.Ioi 0) := by
  apply MeasureTheory.LocallyIntegrableOn.congr _
    (realPrimalTheta_locallyIntegrableOn W d ds)
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
  exact (realPrimal3DBankReadout_eq_theta W d ds hx).symm

theorem realDual3DReflectedReadout_locallyIntegrableOn (W : PolynomialSatakeDualPair ι)
    (d : ℂ) (ds : List ℂ) :
    MeasureTheory.LocallyIntegrableOn
      (fun x : ℝ => realDual3DTransformedReadout W d ds (1 / x)) (Set.Ioi 0) := by
  apply MeasureTheory.LocallyIntegrableOn.congr _
    (realDualTheta_locallyIntegrableOn W d ds)
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
  have hxpos : 0 < x := Set.mem_Ioi.mp hx
  rw [realDual3DTransformedReadout_eq_theta_one_div W d ds (one_div_pos.mpr hxpos)]
  simp

theorem realPrimal3DBankReadout_rapid (W : PolynomialSatakeDualPair ι)
    (d : ℂ) (ds : List ℂ) :
    ∀ q : ℝ, realPrimal3DBankReadout W d ds =O[atTop] (fun x : ℝ => x ^ q) := by
  let A : ℝ := (Fintype.card ι + W.primalExponent : ℕ)
  have ha : ∀ n : ℕ, ‖cpsPolynomialPrimalCoeff W n‖ ≤
      (1 : ℝ) * (((n + 1 : ℕ) : ℝ) ^ A) := by
    intro n
    change ‖cpsPolynomialPrimalCoeff W n‖ ≤
      1 * (((n + 1 : ℕ) : ℝ) ^
        ((Fintype.card ι + W.primalExponent : ℕ) : ℝ))
    rw [one_mul, Real.rpow_natCast]
    exact cpsPolynomialPrimalCoeff_norm_le W n
  have htheta := CriticalLinePhasor.CarrierTheta.theta_rapid_of_polynomial_of_kernel_rapid
    (cpsPolynomialPrimalCoeff W) (realChainKernelLog d ds)
      1 A zero_le_one ha (realChainKernelLog_rapid d ds)
  intro q
  have heq :
      CriticalLinePhasor.CarrierTheta.theta (cpsPolynomialPrimalCoeff W)
          (realChainKernelLog d ds) =ᶠ[atTop]
        realPrimal3DBankReadout W d ds := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact (realPrimal3DBankReadout_eq_theta W d ds hx).symm
  simpa using (htheta q).congr' heq Filter.EventuallyEq.rfl

theorem realDual3DReflectedReadout_rapid (W : PolynomialSatakeDualPair ι)
    (d : ℂ) (ds : List ℂ) :
    ∀ q : ℝ,
      (fun x : ℝ => realDual3DTransformedReadout W d ds (1 / x))
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
  have htheta := CriticalLinePhasor.CarrierTheta.theta_rapid_of_polynomial_of_kernel_rapid
    (cpsPolynomialDualCoeff W) (realChainKernelLog d ds)
      1 A zero_le_one ha (realChainKernelLog_rapid d ds)
  intro q
  have heq :
      CriticalLinePhasor.CarrierTheta.theta (cpsPolynomialDualCoeff W)
          (realChainKernelLog d ds) =ᶠ[atTop]
        (fun x : ℝ => realDual3DTransformedReadout W d ds (1 / x)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [realDual3DTransformedReadout_eq_theta_one_div W d ds (one_div_pos.mpr hx)]
    simp
  simpa using (htheta q).congr' heq Filter.EventuallyEq.rfl

/-- The pure-real completed readout. -/
noncomputable def realPrimalCompletedReadout (W : PolynomialSatakeDualPair ι)
    (d : ℂ) (ds : List ℂ) (s : ℂ) : ℂ :=
  (((d :: ds).map fun e => Complex.Gammaℝ (s + e)).prod) *
    CriticalLinePhasor.CarrierTheta.dirichlet (cpsPolynomialPrimalCoeff W) s

noncomputable def realDualCompletedReadout (W : PolynomialSatakeDualPair ι)
    (d : ℂ) (ds : List ℂ) (s : ℂ) : ℂ :=
  (((d :: ds).map fun e => Complex.Gammaℝ (s + e)).prod) *
    CriticalLinePhasor.CarrierTheta.dirichlet (cpsPolynomialDualCoeff W) s

theorem realPrimal3D_initialIdentification (W : PolynomialSatakeDualPair ι)
    (d : ℂ) (ds : List ℂ) (s : ℂ)
    (hd : 0 < (s + d).re) (hds : ∀ e ∈ ds, 0 < (s + e).re)
    (hs : ((Fintype.card ι + W.primalExponent : ℕ) : ℝ) + 1 < s.re) :
    mellin (realPrimal3DBankReadout W d ds) s =
      realPrimalCompletedReadout W d ds s := by
  have heq : mellin (realPrimal3DBankReadout W d ds) s =
      mellin (CriticalLinePhasor.CarrierTheta.theta (cpsPolynomialPrimalCoeff W)
        (realChainKernelLog d ds)) s := by
    unfold mellin
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp only
    rw [realPrimal3DBankReadout_eq_theta W d ds (Set.mem_Ioi.mp hx)]
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
  have hg := realChainKernelLog_hasMellin d ds s hd hds
  have h := CriticalLinePhasor.CarrierTheta.theta_hasMellin_of_polynomial
    (cpsPolynomialPrimalCoeff W) (realChainKernelLog d ds)
      s 1 A hg.1 ha (by simpa [A] using hs)
  rw [h.2, hg.2]
  unfold realPrimalCompletedReadout
  ring

theorem realDual3D_initialIdentification (W : PolynomialSatakeDualPair ι)
    (d : ℂ) (ds : List ℂ) (s : ℂ)
    (hd : 0 < (s + d).re) (hds : ∀ e ∈ ds, 0 < (s + e).re)
    (hs : ((Fintype.card ι + W.dualExponent : ℕ) : ℝ) + 1 < s.re) :
    mellin (fun x : ℝ => realDual3DTransformedReadout W d ds (1 / x)) s =
      realDualCompletedReadout W d ds s := by
  have heq : mellin (fun x : ℝ => realDual3DTransformedReadout W d ds (1 / x)) s =
      mellin (CriticalLinePhasor.CarrierTheta.theta (cpsPolynomialDualCoeff W)
        (realChainKernelLog d ds)) s := by
    unfold mellin
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    have hxpos : 0 < x := Set.mem_Ioi.mp hx
    dsimp only
    rw [realDual3DTransformedReadout_eq_theta_one_div W d ds (one_div_pos.mpr hxpos)]
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
  have hg := realChainKernelLog_hasMellin d ds s hd hds
  have h := CriticalLinePhasor.CarrierTheta.theta_hasMellin_of_polynomial
    (cpsPolynomialDualCoeff W) (realChainKernelLog d ds)
      s 1 A hg.1 ha (by simpa [A] using hs)
  rw [h.2, hg.2]
  unfold realDualCompletedReadout
  ring

end CriticalLinePhasor.GlobalHelix

namespace CriticalLinePhasor.RealChainMechanism

open CriticalLinePhasor.GlobalHelix CriticalLinePhasor.TransportClosure
open CriticalLinePhasor.ThetaMechanism CriticalLinePhasor.CarrierTheta
open CriticalLinePhasor.GeneralSeed
open Set Filter Topology MeasureTheory Asymptotics

variable {ι : Type*} [Fintype ι]

/-- The typed conclusion at a pure-real chart: entire continuation, functional
equation, and the `∏Γℝ` chart identification. -/
structure RealNicePackage (a : ArithmeticFunction ℂ) (d : ℂ) (ds : List ℂ)
    (B : ℝ) (ε : ℂ) where
  lam : ℂ → ℂ
  entire : Differentiable ℂ lam
  FE : ∀ s : ℂ, lam (1 - s) = ε * lam s
  chart : ∀ s : ℂ, B < s.re →
    lam s = (((d :: ds).map fun e => Complex.Gammaℝ (s + e)).prod) * LSeries (⇑a) s

/-- Uniqueness of the pure-real continuation. -/
theorem RealNicePackage.unique {a : ArithmeticFunction ℂ} {d : ℂ} {ds : List ℂ}
    {B : ℝ} {ε ε' : ℂ}
    (P : RealNicePackage a d ds B ε) (Q : RealNicePackage a d ds B ε') :
    P.lam = Q.lam := by
  refine CriticalLinePhasor.CarrierTargetIdentification.entire_eq_of_eqOn_isOpen
    P.entire Q.entire
    (U := {s : ℂ | B < s.re})
    (IsOpen.preimage Complex.continuous_re isOpen_Ioi)
    (z₀ := ((B + 1 : ℝ) : ℂ))
    (by simp only [Set.mem_setOf_eq, Complex.ofReal_re]; linarith)
    ?_
  intro s hs
  simp only [Set.mem_setOf_eq] at hs
  rw [P.chart s hs, Q.chart s hs]

/-- **THE MECHANISM AT A PURE-REAL CHART** — the Maass chart type: one theta identity
of the prescribed chain readouts yields the complete package. -/
noncomputable def mechanismRR (W : PolynomialSatakeDualPair ι)
    (hdual : ∀ j : ℕ, cpsPolynomialDualCoeff W j = cpsPolynomialPrimalCoeff W j)
    (d : ℂ) (hd : 0 ≤ d.re) (ds : List ℂ) (hds : ∀ e ∈ ds, 0 ≤ e.re)
    (ε : ℂ) (hε : ε ≠ 0)
    (hrefl : ∀ x : ℝ, 0 < x →
      realPrimal3DBankReadout W d ds (1 / x) =
        (ε * ((x ^ (1 : ℝ) : ℝ) : ℂ)) •
          realDual3DTransformedReadout W d ds (1 / x)) :
    RealNicePackage (coefficientArithmetic (cpsPolynomialPrimalCoeff W)) d ds
      (mechB W) ε := by
  refine
    let pair : StrongFEPair ℂ :=
      { f := realPrimal3DBankReadout W d ds
        g := fun x : ℝ => realDual3DTransformedReadout W d ds (1 / x)
        k := 1
        ε := ε
        f₀ := 0
        g₀ := 0
        hf_int := realPrimal3DBankReadout_locallyIntegrableOn W d ds
        hg_int := realDual3DReflectedReadout_locallyIntegrableOn W d ds
        hk := one_pos
        hε := hε
        h_feq := fun x hx => hrefl x hx
        hf_top := fun q => by
          simpa using realPrimal3DBankReadout_rapid W d ds q
        hg_top := fun q => by
          simpa using realDual3DReflectedReadout_rapid W d ds q
        hf₀ := rfl
        hg₀ := rfl }
    ?_
  have hconds : ∀ s : ℂ, mechB W < s.re →
      (0 < (s + d).re ∧ (∀ e ∈ ds, 0 < (s + e).re) ∧
        ((Fintype.card ι + W.primalExponent : ℕ) : ℝ) + 1 < s.re ∧
        ((Fintype.card ι + W.dualExponent : ℕ) : ℝ) + 1 < s.re) := by
    intro s hs
    have h1 : (1 : ℝ) ≤ mechB W := by
      unfold mechB
      have : (0 : ℝ) ≤ ((Fintype.card ι + max W.primalExponent W.dualExponent : ℕ) : ℝ) := by
        positivity
      linarith
    refine ⟨by simp only [Complex.add_re]; linarith, fun e he => ?_, ?_, ?_⟩
    · have := hds e he
      simp only [Complex.add_re]
      linarith
    · have hle : ((Fintype.card ι + W.primalExponent : ℕ) : ℝ)
          ≤ ((Fintype.card ι + max W.primalExponent W.dualExponent : ℕ) : ℝ) := by
        push_cast
        have : (W.primalExponent : ℝ) ≤ (max W.primalExponent W.dualExponent : ℝ) := by
          exact_mod_cast le_max_left W.primalExponent W.dualExponent
        linarith
      unfold mechB at hs
      linarith
    · have hle : ((Fintype.card ι + W.dualExponent : ℕ) : ℝ)
          ≤ ((Fintype.card ι + max W.primalExponent W.dualExponent : ℕ) : ℝ) := by
        push_cast
        have : (W.dualExponent : ℝ) ≤ (max W.primalExponent W.dualExponent : ℝ) := by
          exact_mod_cast le_max_right W.primalExponent W.dualExponent
        linarith
      unfold mechB at hs
      linarith
  have hsymm : pair.symm.Λ = pair.Λ := by
    refine CriticalLinePhasor.CarrierTargetIdentification.entire_eq_of_eqOn_isOpen
      pair.symm.differentiable_Λ pair.differentiable_Λ
      (U := {s : ℂ | mechB W < s.re})
      (IsOpen.preimage Complex.continuous_re isOpen_Ioi)
      (z₀ := ((mechB W + 1 : ℝ) : ℂ))
      (by
        have h1 : (1 : ℝ) ≤ mechB W := by
          unfold mechB
          have : (0 : ℝ) ≤ ((Fintype.card ι + max W.primalExponent W.dualExponent : ℕ) : ℝ) := by
            positivity
          linarith
        simp only [Set.mem_setOf_eq, Complex.ofReal_re]
        linarith)
      ?_
    intro s hs
    simp only [Set.mem_setOf_eq] at hs
    obtain ⟨hc1, hc2, hc3, hc4⟩ := hconds s hs
    have hid1 := realPrimal3D_initialIdentification W d ds s hc1 hc2 hc3
    have hid2 := realDual3D_initialIdentification W d ds s hc1 hc2 hc4
    have hdualdir : dirichlet (cpsPolynomialDualCoeff W) s
        = dirichlet (cpsPolynomialPrimalCoeff W) s := by
      unfold dirichlet
      exact tsum_congr fun m => by rw [hdual m]
    refine (hid2.trans ?_).trans hid1.symm
    unfold realDualCompletedReadout realPrimalCompletedReadout
    rw [hdualdir]
  exact
    { lam := pair.Λ
      entire := pair.differentiable_Λ
      FE := by
        intro s
        have h := pair.functional_equation s
        rw [hsymm] at h
        rw [show ((pair.k : ℝ) : ℂ) = 1 from by norm_num] at h
        simpa using h
      chart := by
        intro s hs
        obtain ⟨hc1, hc2, hc3, _⟩ := hconds s hs
        have hid := realPrimal3D_initialIdentification W d ds s hc1 hc2 hc3
        refine hid.trans ?_
        unfold realPrimalCompletedReadout
        have hcoeff : cpsPolynomialPrimalCoeff W
            = fun j => (coefficientArithmetic (cpsPolynomialPrimalCoeff W)) (j + 1) := by
          funext j
          simp [coefficientArithmetic]
        rw [hcoeff, dirichlet_shift_eq_LSeries _ (bankArithmetic_summable W hs)]
        rw [← hcoeff] }

/-- **The mechanism at every rank over every seed at pure-real charts** — the Maass
symmetric powers' chart type: one theta identity yields the complete package. -/
noncomputable def symr_real_package_of_theta_of (S : SatakeSeed) (r : ℕ)
    (d : ℂ) (hd : 0 ≤ d.re) (ds : List ℂ) (hds : ∀ e ∈ ds, 0 ≤ e.re)
    (ε : ℂ) (hε : ε ≠ 0)
    (hrefl : ∀ x : ℝ, 0 < x →
      realPrimal3DBankReadout (symrSatakePairOf S r) d ds (1 / x) =
        (ε * ((x ^ (1 : ℝ) : ℝ) : ℂ)) •
          realDual3DTransformedReadout (symrSatakePairOf S r) d ds (1 / x)) :
    RealNicePackage (coefficientArithmetic (cpsPolynomialPrimalCoeff (symrSatakePairOf S r)))
      d ds (mechB (symrSatakePairOf S r)) ε :=
  mechanismRR (symrSatakePairOf S r) (symrPairOf_dual_eq_primal S r) d hd ds hds ε hε hrefl

/-- The Maass spectral chart for `Sym^r` at spectral parameter `t`: the `r + 1`
purely imaginary shifts `(r - 2j)·it`, `j = 0, …, r` — the tempered
principal-series readout of the strand pair `(e^{it}, e^{-it})` under `Sym^r`. -/
noncomputable def maassHead (r : ℕ) (t : ℝ) : ℂ := (((r : ℝ) * t : ℝ) : ℂ) * Complex.I

noncomputable def maassTail (r : ℕ) (t : ℝ) : List ℂ :=
  (List.range r).map fun j => ((((r : ℝ) - 2 * (j + 1)) * t : ℝ) : ℂ) * Complex.I

theorem maassHead_re (r : ℕ) (t : ℝ) : (maassHead r t).re = 0 := by
  simp [maassHead]

theorem maassTail_re (r : ℕ) (t : ℝ) : ∀ e ∈ maassTail r t, e.re = 0 := by
  intro e he
  unfold maassTail at he
  simp only [List.mem_map] at he
  obtain ⟨j, _, rfl⟩ := he
  simp

/-- **The Maass instance**: the mechanism for `Sym^r` of any Maass–Hecke seed at its
own spectral chart — the `r + 1` shifts `(r - 2j)·it`.  One theta identity of the
prescribed pure-real chain readouts yields entirety, the functional equation, and
the `∏_{j} Γℝ(s + (r-2j)it)` chart identification, at every rank `r`. -/
noncomputable def maass_symr_package_of_theta (M : MaassEigenData) (r : ℕ) (t : ℝ)
    (ε : ℂ) (hε : ε ≠ 0)
    (hrefl : ∀ x : ℝ, 0 < x →
      realPrimal3DBankReadout (symrSatakePairOf (SatakeSeed.ofMaass M) r)
          (maassHead r t) (maassTail r t) (1 / x) =
        (ε * ((x ^ (1 : ℝ) : ℝ) : ℂ)) •
          realDual3DTransformedReadout (symrSatakePairOf (SatakeSeed.ofMaass M) r)
            (maassHead r t) (maassTail r t) (1 / x)) :
    RealNicePackage
      (coefficientArithmetic
        (cpsPolynomialPrimalCoeff (symrSatakePairOf (SatakeSeed.ofMaass M) r)))
      (maassHead r t) (maassTail r t)
      (mechB (symrSatakePairOf (SatakeSeed.ofMaass M) r)) ε :=
  symr_real_package_of_theta_of (SatakeSeed.ofMaass M) r
    (maassHead r t) (le_of_eq (maassHead_re r t).symm)
    (maassTail r t) (fun e he => le_of_eq (maassTail_re r t e he).symm)
    ε hε hrefl

end CriticalLinePhasor.RealChainMechanism

#print axioms CriticalLinePhasor.GlobalHelix.realChainKernelLog_hasMellin
#print axioms CriticalLinePhasor.GlobalHelix.realPrimal3D_initialIdentification
#print axioms CriticalLinePhasor.RealChainMechanism.RealNicePackage.unique
#print axioms CriticalLinePhasor.RealChainMechanism.mechanismRR
#print axioms CriticalLinePhasor.RealChainMechanism.symr_real_package_of_theta_of
#print axioms CriticalLinePhasor.RealChainMechanism.maass_symr_package_of_theta
