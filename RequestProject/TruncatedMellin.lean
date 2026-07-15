import RequestProject.RSMaster

/-!
# The truncated theta transform: explicit bounds for the continuation

Continuation, part one.  The truncated bank `truncTheta z = (Θ_z - 1)·𝟙_{(1,∞)}` has a Mellin
transform converging at **every** `s ∈ ℂ` (`truncMellin_convergent` — exponential decay above
`t = 1`, identically zero below), with the explicit norm bound (`truncMellin_norm_le`)

  `‖mellin (truncTheta z) w‖ ≤ Kz z · (π·cz z)^{-N} · Γ(N)`   for `Re w ≤ N`,

where `cz z` is the compiled trace rate and `Kz z = e^{π·cz}·Θ_z(1)` the compiled amplitude
(`theta_tail_bound`, the cusp estimate re-derived standalone).  These are the z-explicit
ingredients for differentiating the master equation's left side under the `𝒟`-integral:
`Λ₀_z` will decompose as `truncMellin z s + truncMellin z (1-s)` by the compiled weld.
No RH/GRH.
-/

open MeasureTheory Complex UpperHalfPlane Set Filter Asymptotics
open scoped Real Topology

namespace CriticalLinePhasor.Unfolding

open CriticalLinePhasor.EpsteinTheta

/-- The cusp rate: the compiled trace constant. -/
noncomputable def cz (z : ℍ) : ℝ := z.im / (z.re ^ 2 + z.im ^ 2 + 1)

/-- The cusp amplitude. -/
noncomputable def Kz (z : ℍ) : ℝ := Real.exp (π * cz z) * latticeTheta z 1

lemma cz_pos (z : ℍ) : 0 < cz z := by
  have := z.im_pos
  rw [cz]
  positivity

/-- The bank dominates its DC term. -/
lemma one_le_latticeTheta (z : ℍ) {t : ℝ} (ht : 0 < t) : 1 ≤ latticeTheta z t := by
  have hsummable := summable_latticeTheta_term z ht
  have h0 : Real.exp (-(π * t) * gram z 0) = 1 := by
    rw [gram_zero, mul_zero, Real.exp_zero]
  rw [latticeTheta, ← h0]
  exact hsummable.le_tsum 0 fun p _ => (Real.exp_pos _).le

lemma Kz_pos (z : ℍ) : 0 < Kz z := by
  have h1 := one_le_latticeTheta z one_pos
  rw [Kz]
  positivity

/-- **The cusp tail bound**, standalone: above height one the bank tail decays exponentially
at the trace rate, with amplitude `Kz`. -/
lemma theta_tail_bound (z : ℍ) {t : ℝ} (ht : 1 ≤ t) :
    latticeTheta z t - 1 ≤ Kz z * Real.exp (-(π * cz z) * t) := by
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht
  have hcpos := cz_pos z
  have hnn : ∀ p : ℤ × ℤ,
      0 ≤ ite (p = 0) 0 (Real.exp (-(π * t) * gram z p)) := by
    intro p
    by_cases hp : p = 0
    · rw [if_pos hp]
    · rw [if_neg hp]
      positivity
  have hsplit : latticeTheta z t - 1 =
      ∑' p : ℤ × ℤ, ite (p = 0) 0 (Real.exp (-(π * t) * gram z p)) := by
    have h := (summable_latticeTheta_term z ht0).tsum_eq_add_tsum_ite (0 : ℤ × ℤ)
    simp only [gram_zero, mul_zero, Real.exp_zero] at h
    rw [latticeTheta, h]
    ring
  have hterm : ∀ p : ℤ × ℤ,
      ite (p = 0) 0 (Real.exp (-(π * t) * gram z p)) ≤
        Real.exp (-(π * cz z) * (t - 1)) * Real.exp (-(π * 1) * gram z p) := by
    intro p
    by_cases hp : p = 0
    · rw [if_pos hp]
      positivity
    · rw [if_neg hp, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hgc : cz z ≤ gram z p := gram_ge_const z hp
      nlinarith [mul_nonneg (mul_nonneg Real.pi_pos.le
        (sub_nonneg.mpr ht)) (sub_nonneg.mpr hgc)]
  have hsum_ite : Summable fun p : ℤ × ℤ =>
      ite (p = 0) 0 (Real.exp (-(π * t) * gram z p)) := by
    refine Summable.of_nonneg_of_le hnn (fun p => ?_)
      (summable_latticeTheta_term z ht0)
    by_cases hp : p = 0
    · rw [if_pos hp]
      positivity
    · rw [if_neg hp]
  have hsum_rhs : Summable fun p : ℤ × ℤ =>
      Real.exp (-(π * cz z) * (t - 1)) * Real.exp (-(π * 1) * gram z p) :=
    (summable_latticeTheta_term z one_pos).mul_left _
  calc latticeTheta z t - 1
      = ∑' p : ℤ × ℤ, ite (p = 0) 0 (Real.exp (-(π * t) * gram z p)) := hsplit
    _ ≤ ∑' p : ℤ × ℤ,
          Real.exp (-(π * cz z) * (t - 1)) * Real.exp (-(π * 1) * gram z p) :=
        Summable.tsum_le_tsum hterm hsum_ite hsum_rhs
    _ = Real.exp (-(π * cz z) * (t - 1)) * latticeTheta z 1 := by
        rw [tsum_mul_left, latticeTheta]
    _ = Kz z * Real.exp (-(π * cz z) * t) := by
        rw [Kz, show -(π * cz z) * (t - 1) = π * cz z + -(π * cz z) * t by ring,
          Real.exp_add]
        ring

/-- The truncated bank: the tail of the theta above height one. -/
noncomputable def truncTheta (z : ℍ) : ℝ → ℂ :=
  (Set.Ioi (1 : ℝ)).indicator fun t => latticeThetaC z t - 1

/-- Pointwise norm bound for the truncated bank. -/
lemma truncTheta_norm_le (z : ℍ) (t : ℝ) :
    ‖truncTheta z t‖ ≤
      (Set.Ioi (1 : ℝ)).indicator
        (fun t => Kz z * Real.exp (-(π * cz z) * t)) t := by
  by_cases h : t ∈ Set.Ioi (1 : ℝ)
  · rw [truncTheta, indicator_of_mem h, indicator_of_mem h]
    have ht1 : (1 : ℝ) ≤ t := le_of_lt h
    have hth := one_le_latticeTheta z (lt_of_lt_of_le one_pos ht1)
    rw [latticeThetaC, show ((latticeTheta z t : ℂ) - 1) =
      ((latticeTheta z t - 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_of_nonneg (by linarith)]
    exact theta_tail_bound z ht1
  · rw [truncTheta, indicator_of_notMem h, indicator_of_notMem h, norm_zero]

/-- The truncated bank is locally integrable on the half-line. -/
lemma truncTheta_locallyIntegrable (z : ℍ) :
    LocallyIntegrableOn (truncTheta z) (Set.Ioi (0 : ℝ)) := by
  have hcont : LocallyIntegrableOn (fun t => latticeThetaC z t - 1)
      (Set.Ioi (0 : ℝ)) := by
    refine ContinuousOn.locallyIntegrableOn ?_ measurableSet_Ioi
    exact ((Complex.continuous_ofReal.comp_continuousOn
      (continuousOn_latticeTheta z)).sub continuousOn_const)
  intro x hx
  obtain ⟨s, hs, hs'⟩ := hcont x hx
  exact ⟨s, hs, hs'.indicator measurableSet_Ioi⟩

/-- The truncated bank vanishes near zero. -/
lemma truncTheta_eventually_zero (z : ℍ) :
    (truncTheta z) =ᶠ[𝓝[>] (0 : ℝ)] 0 := by
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one)] with t ht
  rw [truncTheta, indicator_of_notMem (by
    rw [Set.mem_Ioi, not_lt]
    exact ht.2.le)]
  rfl

/-- The truncated bank decays like any power at infinity. -/
lemma truncTheta_isBigO_top (z : ℍ) (a : ℝ) :
    (truncTheta z) =O[atTop] (· ^ (-a)) := by
  have h1 : (truncTheta z) =O[atTop] fun t => Real.exp (-(π * cz z) * t) := by
    rw [isBigO_iff]
    refine ⟨Kz z, ?_⟩
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    calc ‖truncTheta z t‖ ≤ (Set.Ioi (1 : ℝ)).indicator
          (fun t => Kz z * Real.exp (-(π * cz z) * t)) t := truncTheta_norm_le z t
      _ ≤ Kz z * Real.exp (-(π * cz z) * t) := by
          by_cases h : t ∈ Set.Ioi (1 : ℝ)
          · rw [indicator_of_mem h]
          · rw [indicator_of_notMem h]
            exact mul_nonneg (Kz_pos z).le (Real.exp_pos _).le
  exact h1.trans (exp_neg_isBigO_rpow (by have := cz_pos z; positivity) (-a))

/-- **The truncated Mellin transform converges at every `s`.** -/
lemma truncMellin_convergent (z : ℍ) (w : ℂ) :
    MellinConvergent (truncTheta z) w := by
  refine mellinConvergent_of_isBigO_rpow (a := w.re + 1) (b := w.re - 1)
    (truncTheta_locallyIntegrable z) (truncTheta_isBigO_top z (w.re + 1))
    (by linarith) ?_ (by linarith)
  exact (truncTheta_eventually_zero z).trans_isBigO (isBigO_zero _ _)

/-- The Gamma-type dominant is integrable at every positive rate. -/
lemma integrableOn_rpow_mul_exp_neg {N r : ℝ} (hN : 0 < N) (hr : 0 < r) :
    IntegrableOn (fun t : ℝ => t ^ (N - 1) * Real.exp (-(r * t)))
      (Set.Ioi (0 : ℝ)) := by
  have h2 : IntegrableOn (fun x : ℝ => Real.exp (-(r * x)) * (r * x) ^ (N - 1))
      (Set.Ioi (0 : ℝ)) := by
    have h3 := (integrableOn_Ioi_comp_mul_left_iff
      (fun x : ℝ => Real.exp (-x) * x ^ (N - 1)) 0 hr).mpr
    rw [mul_zero] at h3
    exact h3 (Real.GammaIntegral_convergent hN)
  have h4 := h2.const_mul ((r ^ (N - 1))⁻¹)
  refine MeasureTheory.IntegrableOn.congr_fun h4 (fun t ht => ?_) measurableSet_Ioi
  rw [Real.mul_rpow hr.le (le_of_lt ht)]
  field_simp [(Real.rpow_pos_of_pos hr (N - 1)).ne']

/-- **The explicit norm bound for the truncated Mellin transform**: uniform for
`Re w ≤ N`. -/
lemma truncMellin_norm_le (z : ℍ) {w : ℂ} {N : ℝ} (hN : 0 < N) (hw : w.re ≤ N) :
    ‖mellin (truncTheta z) w‖ ≤
      Kz z * ((1 / (π * cz z)) ^ N * Real.Gamma N) := by
  have hc := cz_pos z
  have hrate : (0 : ℝ) < π * cz z := by positivity
  calc ‖mellin (truncTheta z) w‖
      ≤ ∫ t in Set.Ioi (0 : ℝ), ‖(t : ℂ) ^ (w - 1) • truncTheta z t‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ t in Set.Ioi (0 : ℝ), Kz z *
          (t ^ (N - 1) * Real.exp (-(π * cz z * t))) := by
        refine setIntegral_mono_on (truncMellin_convergent z w).norm
          ((integrableOn_rpow_mul_exp_neg hN hrate).const_mul (Kz z))
          measurableSet_Ioi (fun t ht => ?_)
        have ht0 : (0 : ℝ) < t := ht
        rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.sub_re,
          Complex.one_re]
        calc t ^ (w.re - 1) * ‖truncTheta z t‖
            ≤ t ^ (w.re - 1) * (Set.Ioi (1 : ℝ)).indicator
              (fun t => Kz z * Real.exp (-(π * cz z) * t)) t :=
              mul_le_mul_of_nonneg_left (truncTheta_norm_le z t)
                (Real.rpow_nonneg ht0.le _)
          _ ≤ Kz z * (t ^ (N - 1) * Real.exp (-(π * cz z * t))) := by
              by_cases h1 : t ∈ Set.Ioi (1 : ℝ)
              · rw [indicator_of_mem h1]
                have ht1 : (1 : ℝ) ≤ t := le_of_lt h1
                have hexp : Real.exp (-(π * cz z) * t) =
                    Real.exp (-(π * cz z * t)) := by
                  congr 1
                  ring
                rw [hexp, show t ^ (w.re - 1) *
                    (Kz z * Real.exp (-(π * cz z * t))) =
                    Kz z * (t ^ (w.re - 1) * Real.exp (-(π * cz z * t))) by ring]
                apply mul_le_mul_of_nonneg_left _ (Kz_pos z).le
                apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
                exact Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)
              · rw [indicator_of_notMem h1, mul_zero]
                have := Kz_pos z
                positivity
    _ = Kz z * ((1 / (π * cz z)) ^ N * Real.Gamma N) := by
        rw [MeasureTheory.integral_const_mul]
        exact congrArg _ (Real.integral_rpow_mul_exp_neg_mul_Ioi hN hrate)

end CriticalLinePhasor.Unfolding

#print axioms CriticalLinePhasor.Unfolding.theta_tail_bound
#print axioms CriticalLinePhasor.Unfolding.truncMellin_convergent
#print axioms CriticalLinePhasor.Unfolding.truncMellin_norm_le
