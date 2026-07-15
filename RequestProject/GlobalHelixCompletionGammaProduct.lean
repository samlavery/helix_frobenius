import RequestProject.GlobalHelixLogMellinConvolution

/-!
# The complete fixed archimedean Gamma product

Every archimedean clock is fixed before the Euler bank is attached.  Signed-log convolution
assembles the clocks, and the Mellin product theorem identifies the resulting kernel with the full
product of Deligne Gamma factors.  Positive height scaling contributes the conductor factor.
-/

open Complex Set Filter Topology MeasureTheory Asymptotics

namespace CriticalLinePhasor.GlobalHelix

/-- Every single fixed Gamma clock decreases faster than every real power at positive infinity. -/
theorem gammaClock_rapid (μ : ℂ) :
    ∀ q : ℝ, gammaClock μ =O[atTop] (fun x : ℝ => x ^ q) := by
  intro q
  have hdec :=
    (isLittleO_exp_neg_mul_rpow_atTop
      (a := 2 * Real.pi) (by positivity) (q - μ.re)).isBigO
  rw [isBigO_iff'] at hdec ⊢
  obtain ⟨C, hC, hbound⟩ := hdec
  refine ⟨2 * C, mul_pos (by norm_num) hC, ?_⟩
  filter_upwards [hbound, eventually_gt_atTop (1 : ℝ)] with x hxdec hx1
  have hx : 0 < x := zero_lt_one.trans hx1
  have hxpow : x ^ μ.re * x ^ (q - μ.re) = x ^ q := by
    rw [← Real.rpow_add hx]
    congr 1
    ring
  have hnorm : ‖gammaClock μ x‖ =
      2 * x ^ μ.re * Real.exp (-(2 * Real.pi) * x) := by
    rw [gammaClock, norm_mul, norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.norm_exp]
    norm_num
  rw [hnorm, Real.norm_of_nonneg (Real.rpow_nonneg hx.le q)]
  calc
    2 * x ^ μ.re * Real.exp (-(2 * Real.pi) * x) ≤
        2 * x ^ μ.re * (C * x ^ (q - μ.re)) := by
      gcongr
      simpa [Real.norm_of_nonneg (Real.exp_nonneg _),
        Real.norm_of_nonneg (Real.rpow_nonneg hx.le _)] using hxdec
    _ = (2 * C) * x ^ q := by rw [← hxpow]; ring

/-- A positive power times a negative exponential has an explicit global bound. -/
theorem rpow_mul_exp_neg_le_exp_log_ratio
    {a c x : ℝ} (ha : 0 < a) (hc : 0 < c) (hx : 0 < x) :
    x ^ a * Real.exp (-c * x) ≤
      Real.exp (a * (Real.log (a / c) - 1)) := by
  have hay : 0 < c * x / a := div_pos (mul_pos hc hx) ha
  have hratio : 0 < a / c := div_pos ha hc
  have hprod : (a / c) * (c * x / a) = x := by
    field_simp
  have hlog : Real.log x =
      Real.log (a / c) + Real.log (c * x / a) := by
    rw [← Real.log_mul hratio.ne' hay.ne', hprod]
  rw [Real.rpow_def_of_pos hx, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  rw [hlog]
  have hbasic := Real.log_le_sub_one_of_pos hay
  have hscaled : a * Real.log (c * x / a) ≤ c * x - a := by
    calc
      a * Real.log (c * x / a) ≤ a * (c * x / a - 1) :=
        mul_le_mul_of_nonneg_left hbasic ha.le
      _ = c * x - a := by field_simp
  nlinarith

/-- Exact norm of one real-Mellin-weighted Gamma clock in signed-log height. -/
theorem weightedGammaLogProfile_norm_eq
    (μ : ℂ) (s u : ℝ) :
    ‖Complex.exp (-(s : ℂ) * u) * gammaClock μ (Real.exp (-u))‖ =
      2 * (Real.exp (-u)) ^ (s + μ.re) *
        Real.exp (-(2 * Real.pi) * Real.exp (-u)) := by
  have ht : 0 < Real.exp (-u) := Real.exp_pos _
  rw [norm_mul, Complex.norm_exp, gammaClock, norm_mul, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.norm_exp]
  norm_num
  have hcexp : (Complex.exp (-(u : ℂ))).re = Real.exp (-u) := by
    rw [show -(u : ℂ) = ((-u : ℝ) : ℂ) by push_cast; rfl,
      Complex.exp_ofReal_re]
  rw [hcexp]
  have hsPow : Real.exp (-(s * u)) = (Real.exp (-u)) ^ s := by
    rw [Real.rpow_def_of_pos ht, Real.log_exp]
    congr 1
    ring
  rw [hsPow]
  calc
    Real.exp (-u) ^ s *
        (2 * Real.exp (-u) ^ μ.re * Real.exp (-(2 * Real.pi * Real.exp (-u)))) =
        2 * (Real.exp (-u) ^ s * Real.exp (-u) ^ μ.re) *
          Real.exp (-(2 * Real.pi * Real.exp (-u))) := by ring
    _ = 2 * Real.exp (-u) ^ (s + μ.re) *
          Real.exp (-(2 * Real.pi * Real.exp (-u))) := by
      rw [Real.rpow_add ht]

/-- Every sufficiently positive real Mellin weighting makes one Gamma clock uniformly bounded in
signed-log height. -/
theorem weightedGammaLogProfile_bounded
    (μ : ℂ) (s : ℝ) (hs : 0 < s + μ.re) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ u : ℝ,
      ‖Complex.exp (-(s : ℂ) * u) * gammaClock μ (Real.exp (-u))‖ ≤ B := by
  refine ⟨2 * Real.exp ((s + μ.re) *
      (Real.log ((s + μ.re) / (2 * Real.pi)) - 1)), by positivity, ?_⟩
  intro u
  rw [weightedGammaLogProfile_norm_eq]
  calc
    2 * Real.exp (-u) ^ (s + μ.re) *
        Real.exp (-(2 * Real.pi) * Real.exp (-u)) =
        2 * (Real.exp (-u) ^ (s + μ.re) *
          Real.exp (-(2 * Real.pi) * Real.exp (-u))) := by ring
    _ ≤ 2 * Real.exp ((s + μ.re) *
        (Real.log ((s + μ.re) / (2 * Real.pi)) - 1)) := by
      gcongr
      exact rpow_mul_exp_neg_le_exp_log_ratio hs (by positivity) (Real.exp_pos _)

/-- An `L¹` function convolved with a uniformly bounded function is uniformly bounded. -/
theorem norm_convolution_mul_le_of_integrable_of_bound
    (f g : ℝ → ℂ) (hf : Integrable f)
    (B : ℝ) (hg : ∀ u : ℝ, ‖g u‖ ≤ B) (x : ℝ) :
    ‖MeasureTheory.convolution f g (ContinuousLinearMap.mul ℂ ℂ)
      (μ := MeasureTheory.volume) x‖ ≤
      B * ∫ u : ℝ, ‖f u‖ := by
  rw [MeasureTheory.convolution_def]
  have hdom : Integrable (fun u : ℝ => B * ‖f u‖) := hf.norm.const_mul B
  calc
    ‖∫ u : ℝ, f u * g (x - u)‖ ≤ ∫ u : ℝ, B * ‖f u‖ := by
      apply norm_integral_le_of_norm_le hdom
      filter_upwards with u
      rw [norm_mul]
      simpa [mul_comm] using
        mul_le_mul_of_nonneg_left (hg (x - u)) (norm_nonneg (f u))
    _ = B * ∫ u : ℝ, ‖f u‖ := by rw [MeasureTheory.integral_const_mul]

/-- A nonempty archimedean clock list assembled in native signed-log height. -/
noncomputable def completionKernelLog : List ℂ → ℝ → ℂ
  | [] => fun _ => 0
  | [μ] => gammaClock μ
  | μ :: ν :: rest => logMellinConvolution (gammaClock μ) (completionKernelLog (ν :: rest))

/-- A common sufficiently positive real Mellin weight makes every finite signed-log Gamma
convolution uniformly bounded. -/
theorem weightedCompletionKernelLog_bounded
    (μs : List ℂ) (hne : μs ≠ []) (s : ℝ)
    (hs : ∀ μ ∈ μs, 0 < s + μ.re) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ u : ℝ,
      ‖Complex.exp (-(s : ℂ) * u) *
        completionKernelLog μs (Real.exp (-u))‖ ≤ B := by
  induction μs with
  | nil => exact (hne rfl).elim
  | cons μ tail ih =>
      cases tail with
      | nil =>
          simpa [completionKernelLog] using
            weightedGammaLogProfile_bounded μ s (hs μ (by simp))
      | cons ν rest =>
          have htail_ne : ν :: rest ≠ [] := by simp
          obtain ⟨B, hB, hbound⟩ := ih htail_ne
            (fun z hz => hs z (by simp [hz]))
          let F : ℝ → ℂ := fun u =>
            Complex.exp (-(s : ℂ) * u) * gammaClock μ (Real.exp (-u))
          let G : ℝ → ℂ := fun u =>
            Complex.exp (-(s : ℂ) * u) *
              completionKernelLog (ν :: rest) (Real.exp (-u))
          have hsμ : 0 < (((s : ℂ) + μ).re) := by
            simpa using hs μ (by simp)
          have hF : Integrable F := by
            exact (mellinConvergent_iff_negLogIntegrable (gammaClock μ) (s : ℂ)).mp
              (gammaClock_mellinConvergent μ (s : ℂ) hsμ)
          refine ⟨B * ∫ u : ℝ, ‖F u‖,
            mul_nonneg hB (integral_nonneg fun _ => norm_nonneg _), ?_⟩
          intro u
          rw [show completionKernelLog (μ :: ν :: rest) =
              logMellinConvolution (gammaClock μ)
                (completionKernelLog (ν :: rest)) by rfl,
            weighted_logMellinConvolution_eq_convolution]
          exact norm_convolution_mul_le_of_integrable_of_bound F G hF B hbound u

/-- A finite shift list and one requested power have a common real Mellin weight above every
near-zero exponent and above the requested decay threshold. -/
theorem exists_weight_gt_neg_and_shifts (q : ℝ) (μs : List ℂ) :
    ∃ s : ℝ, -q < s ∧ ∀ μ ∈ μs, -μ.re < s := by
  induction μs with
  | nil => exact ⟨-q + 1, by linarith, by simp⟩
  | cons μ tail ih =>
      obtain ⟨s, hsq, hs⟩ := ih
      refine ⟨max s (-μ.re) + 1, by linarith [le_max_left s (-μ.re)], ?_⟩
      intro z hz
      simp only [List.mem_cons] at hz
      rcases hz with hz | hz
      · rw [hz]
        linarith [le_max_right s (-μ.re)]
      · linarith [hs z hz, le_max_left s (-μ.re)]

/-- Every finite signed-log convolution of fixed Gamma clocks decreases faster than every real
power at positive infinity. -/
theorem completionKernelLog_rapid (μs : List ℂ) :
    ∀ q : ℝ, completionKernelLog μs =O[atTop] (fun x : ℝ => x ^ q) := by
  intro q
  by_cases hnil : μs = []
  · subst μs
    simpa [completionKernelLog] using
      (isBigO_zero (fun x : ℝ => x ^ q) atTop :
        (fun _ : ℝ => (0 : ℂ)) =O[atTop] (fun x : ℝ => x ^ q))
  obtain ⟨s, hsq, hs⟩ := exists_weight_gt_neg_and_shifts q μs
  have hspos : ∀ μ ∈ μs, 0 < s + μ.re := by
    intro μ hμ
    linarith [hs μ hμ]
  obtain ⟨B, hB, hbound⟩ :=
    weightedCompletionKernelLog_bounded μs hnil s hspos
  rw [isBigO_iff']
  refine ⟨B + 1, by linarith, ?_⟩
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx1
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
  have hraw' : ‖completionKernelLog μs x‖ * x ^ s ≤ B := by
    simpa [mul_comm] using hraw
  have hpow : 0 < x ^ s := Real.rpow_pos_of_pos hx s
  have hk : ‖completionKernelLog μs x‖ ≤ B * x ^ (-s) := by
    have hdiv := (le_div_iff₀ hpow).2 hraw'
    rwa [div_eq_mul_inv, ← Real.rpow_neg hx.le] at hdiv
  calc
    ‖completionKernelLog μs x‖ ≤ B * x ^ (-s) := hk
    _ ≤ (B + 1) * x ^ (-s) := by gcongr; linarith
    _ ≤ (B + 1) * x ^ q := by
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith : -s ≤ q))
        (by linarith)
    _ = (B + 1) * ‖x ^ q‖ := by
      rw [Real.norm_of_nonneg (Real.rpow_nonneg hx.le q)]

/-- The assembled fixed kernel has the complete product of its prescribed Gamma multipliers. -/
theorem completionKernelLog_hasMellin
    (μs : List ℂ) (hne : μs ≠ []) (s : ℂ)
    (hs : ∀ μ ∈ μs, 0 < (s + μ).re) :
    HasMellin (completionKernelLog μs) s
      ((μs.map fun μ => Complex.Gammaℂ (s + μ)).prod) := by
  induction μs with
  | nil => exact (hne rfl).elim
  | cons μ tail ih =>
      cases tail with
      | nil =>
          simpa [completionKernelLog] using
            (show HasMellin (gammaClock μ) s (Complex.Gammaℂ (s + μ)) from
              ⟨gammaClock_mellinConvergent μ s (hs μ (by simp)),
                gammaClock_mellin μ s (hs μ (by simp))⟩)
      | cons ν rest =>
          have hμ : HasMellin (gammaClock μ) s (Complex.Gammaℂ (s + μ)) :=
            ⟨gammaClock_mellinConvergent μ s (hs μ (by simp)),
              gammaClock_mellin μ s (hs μ (by simp))⟩
          have htail := ih (by simp) (fun z hz => hs z (by simp [hz]))
          have hconv := logMellinConvolution_hasMellin
            (gammaClock μ) (completionKernelLog (ν :: rest)) s hμ.1 htail.1
          refine ⟨?_, ?_⟩
          · simpa [completionKernelLog] using hconv.1
          · rw [show completionKernelLog (μ :: ν :: rest) =
                logMellinConvolution (gammaClock μ) (completionKernelLog (ν :: rest)) by rfl,
              hconv.2, hμ.2, htail.2]
            simp

/-- Add the square-root conductor as a geometric scale of the assembled clock. -/
noncomputable def conductorScaledCompletionKernelLog
    (C : ℝ) (μs : List ℂ) (x : ℝ) : ℂ :=
  completionKernelLog μs (x / C)

/-- Positive conductor scaling preserves rapid decay of an arbitrary assembled completion kernel. -/
theorem conductorScaledCompletionKernelLog_rapid_of_rapid
    (C : ℝ) (hC : 0 < C) (μs : List ℂ)
    (hrapid : ∀ q : ℝ, completionKernelLog μs =O[atTop]
      (fun x : ℝ => x ^ q)) :
    ∀ q : ℝ, conductorScaledCompletionKernelLog C μs =O[atTop]
      (fun x : ℝ => x ^ q) := by
  intro q
  have hcomp := (hrapid q).comp_tendsto
    ((tendsto_div_const_atTop_of_pos hC).mpr tendsto_id)
  have heq : (fun x : ℝ => (x / C) ^ q) =ᶠ[atTop]
      (fun x : ℝ => (C ^ q)⁻¹ * x ^ q) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    rw [Real.div_rpow hx hC.le, div_eq_inv_mul]
  have hscale : (fun x : ℝ => (x / C) ^ q) =O[atTop]
      (fun x : ℝ => x ^ q) :=
    heq.trans_isBigO
      (isBigO_const_mul_self (C ^ q)⁻¹ (fun x : ℝ => x ^ q) atTop)
  change (fun x : ℝ => completionKernelLog μs (x / C)) =O[atTop]
    (fun x : ℝ => x ^ q)
  exact hcomp.trans hscale

/-- Every finite prescribed Gamma-product kernel remains rapidly decreasing after its positive
arithmetic conductor scaling. -/
theorem conductorScaledCompletionKernelLog_rapid
    (C : ℝ) (hC : 0 < C) (μs : List ℂ) :
    ∀ q : ℝ, conductorScaledCompletionKernelLog C μs =O[atTop]
      (fun x : ℝ => x ^ q) :=
  conductorScaledCompletionKernelLog_rapid_of_rapid C hC μs
    (completionKernelLog_rapid μs)

/-- Positive conductor scaling preserves rapid decay for each prescribed Gamma clock. -/
theorem conductorScaledCompletionKernelLog_singleton_rapid
    (C : ℝ) (hC : 0 < C) (μ : ℂ) :
    ∀ q : ℝ, conductorScaledCompletionKernelLog C [μ] =O[atTop]
      (fun x : ℝ => x ^ q) := by
  apply conductorScaledCompletionKernelLog_rapid_of_rapid C hC [μ]
  intro q
  change gammaClock μ =O[atTop] (fun x : ℝ => x ^ q)
  exact gammaClock_rapid μ q

/-- The complete fixed kernel reads `C^s` times the full Gamma product. -/
theorem conductorScaledCompletionKernelLog_hasMellin
    (C : ℝ) (hC : 0 < C) (μs : List ℂ) (hne : μs ≠ []) (s : ℂ)
    (hs : ∀ μ ∈ μs, 0 < (s + μ).re) :
    HasMellin (conductorScaledCompletionKernelLog C μs) s
      ((C : ℂ) ^ s * (μs.map fun μ => Complex.Gammaℂ (s + μ)).prod) := by
  have hbase := completionKernelLog_hasMellin μs hne s hs
  have hscale : 0 < C⁻¹ := inv_pos.mpr hC
  have hfun : conductorScaledCompletionKernelLog C μs =
      fun x : ℝ => completionKernelLog μs (C⁻¹ * x) := by
    funext x
    simp [conductorScaledCompletionKernelLog, div_eq_inv_mul]
  have hconv : MellinConvergent (conductorScaledCompletionKernelLog C μs) s := by
    rw [hfun, MellinConvergent.comp_mul_left hscale]
    exact hbase.1
  refine ⟨hconv, ?_⟩
  rw [hfun, mellin_comp_mul_left (completionKernelLog μs) s hscale, hbase.2]
  simp only [smul_eq_mul]
  have hcast : ((C⁻¹ : ℝ) : ℂ) = (C : ℂ)⁻¹ := by push_cast; rfl
  rw [hcast, Complex.inv_cpow _ _ (by
    rw [Complex.arg_ofReal_of_nonneg hC.le]
    exact ne_of_lt Real.pi_pos), Complex.cpow_neg, inv_inv]

end CriticalLinePhasor.GlobalHelix

#print axioms CriticalLinePhasor.GlobalHelix.completionKernelLog_hasMellin
#print axioms CriticalLinePhasor.GlobalHelix.conductorScaledCompletionKernelLog_hasMellin
#print axioms CriticalLinePhasor.GlobalHelix.gammaClock_rapid
#print axioms CriticalLinePhasor.GlobalHelix.weightedCompletionKernelLog_bounded
#print axioms CriticalLinePhasor.GlobalHelix.completionKernelLog_rapid
#print axioms CriticalLinePhasor.GlobalHelix.conductorScaledCompletionKernelLog_rapid_of_rapid
#print axioms CriticalLinePhasor.GlobalHelix.conductorScaledCompletionKernelLog_rapid
#print axioms CriticalLinePhasor.GlobalHelix.conductorScaledCompletionKernelLog_singleton_rapid
