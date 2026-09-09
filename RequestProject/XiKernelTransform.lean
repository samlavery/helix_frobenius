import RequestProject.XiKernelIBP
import RequestProject.ShannonCascade

/-!
# T1a, step 5: `ξ(½ + iz) = ∫ K(u) e^{izu} du` for every `z` (ledger 673)

`Ktrans z = ∫ K(u) e^{izu} du` with `K = Kker` (even, super-exponentially decaying).  Differentiation under the
integral (`hasDerivAt_integral_of_dominated_loc_of_deriv_le`) makes `Ktrans` entire; for `Im z < −½` it equals
`½ s(s−1) Λ(s) = ξ(s)` with `s = ½ + iz` (`xi_integral_form`); the identity theorem finishes.
**`xiSection_eq_Ktrans : xiSection z = Ktrans z`** for all `z` — the kernel representation of the ξ-section.
-/

open Complex Set Filter Topology MeasureTheory CriticalLinePhasor.XiChannel

namespace CriticalLinePhasor.XiKernel

theorem continuous_Kker : Continuous Kker := by
  unfold Kker
  exact (Complex.continuous_exp.comp (Complex.continuous_ofReal.div_const _)).mul
    (continuous_Psi2.add continuous_Psi1)

/-! ### Decay profiles -/

/-- `D_{a,b}(u) = e^{au} exp(−(5/2) e^{2(u−b)})`. -/
noncomputable def Dprof (a b u : ℝ) : ℝ := Real.exp (a * u) * Real.exp (-(5 / 2) * Real.exp (2 * (u - b)))

theorem Dprof_nonneg (a b u : ℝ) : 0 ≤ Dprof a b u := by unfold Dprof; positivity

theorem continuous_Dprof (a b : ℝ) : Continuous (Dprof a b) := by unfold Dprof; fun_prop

theorem integrable_Dprof {a : ℝ} (ha : 0 < a) (b : ℝ) : Integrable (Dprof a b) := by
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := b)]
  refine IntegrableOn.union ?_ ?_
  · have hg : IntegrableOn (fun u : ℝ => Real.exp (a * u)) (Iic b) := integrableOn_exp_mul_Iic ha b
    refine hg.mono' (continuous_Dprof a b).aestronglyMeasurable.restrict ?_
    filter_upwards with u
    rw [Real.norm_eq_abs, abs_of_nonneg (Dprof_nonneg a b u)]
    unfold Dprof
    have : Real.exp (-(5 / 2) * Real.exp (2 * (u - b))) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [Real.exp_pos (2 * (u - b))])
    calc Real.exp (a * u) * Real.exp (-(5 / 2) * Real.exp (2 * (u - b))) ≤ Real.exp (a * u) * 1 := by gcongr
      _ = Real.exp (a * u) := mul_one _
  · exact (integrableOn_decay a b).mono_set Ioi_subset_Ici_self

/-- The even profile `D_{a,b}(|u|)`. -/
noncomputable def Dabs (a b u : ℝ) : ℝ := Dprof a b |u|

theorem Dabs_nonneg (a b u : ℝ) : 0 ≤ Dabs a b u := Dprof_nonneg _ _ _

theorem continuous_Dabs (a b : ℝ) : Continuous (Dabs a b) :=
  (continuous_Dprof a b).comp continuous_abs

theorem integrable_Dabs {a : ℝ} (ha : 0 < a) (b : ℝ) : Integrable (Dabs a b) := by
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
  refine IntegrableOn.union ?_ ?_
  · refine ((integrable_Dprof ha b).comp_neg.integrableOn).congr_fun ?_ measurableSet_Iic
    intro u hu; simp [Dabs, abs_of_nonpos (mem_Iic.mp hu)]
  · refine ((integrable_Dprof ha b).integrableOn).congr_fun ?_ measurableSet_Ioi
    intro u hu; simp [Dabs, abs_of_pos (mem_Ioi.mp hu)]

/-- `D_{a}(|u|) · e^{c|u|} = D_{a+c}(|u|)`. -/
theorem Dabs_mul_exp (a b c u : ℝ) : Dabs a b u * Real.exp (c * |u|) = Dabs (a + c) b u := by
  unfold Dabs Dprof
  rw [show Real.exp (a * |u|) * Real.exp (-(5 / 2) * Real.exp (2 * (|u| - b))) * Real.exp (c * |u|)
      = (Real.exp (a * |u|) * Real.exp (c * |u|)) * Real.exp (-(5 / 2) * Real.exp (2 * (|u| - b))) by ring,
    ← Real.exp_add]
  congr 2; ring

/-! ### Two-sided bound on `K` -/

theorem Kker_abs (u : ℝ) : ‖Kker u‖ = ‖Kker |u|‖ := by
  rcases le_or_gt 0 u with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg h, Kker_even]

/-- `‖K(u)‖ ≤ C · D_{1/2, 2Rc}(u)` for `u ≥ 2Rc`. -/
theorem Kker_bound_pos {u : ℝ} (hu : 2 * Rc ≤ u) :
    ‖Kker u‖ ≤ (2 / Rc ^ 2 + 2 / Rc) * Dprof (1 / 2) (2 * Rc) u := by
  unfold Kker Dprof
  rw [norm_mul, Complex.norm_exp]
  have hre : ((u : ℂ) / 2).re = 1 / 2 * u := by simp; ring
  rw [hre]
  have h2 := Psi2_bound hu
  have h1 : ‖Psi1 u‖ ≤ 2 / Rc * Real.exp (-(5 / 2) * Real.exp (2 * (u - 2 * Rc))) := by
    refine (Psi1_bound (by linarith [Rc_pos])).trans ?_
    have hR := Rc_pos
    have : Real.exp (2 * (u - 2 * Rc)) ≤ Real.exp (2 * (u - Rc)) := Real.exp_le_exp.mpr (by linarith)
    have h' : Real.exp (-(5 / 2) * Real.exp (2 * (u - Rc)))
        ≤ Real.exp (-(5 / 2) * Real.exp (2 * (u - 2 * Rc))) := Real.exp_le_exp.mpr (by linarith)
    exact mul_le_mul_of_nonneg_left h' (by positivity)
  have hsum : ‖Psi2 u + Psi1 u‖ ≤ (2 / Rc ^ 2 + 2 / Rc) * Real.exp (-(5 / 2) * Real.exp (2 * (u - 2 * Rc))) := by
    calc ‖Psi2 u + Psi1 u‖ ≤ ‖Psi2 u‖ + ‖Psi1 u‖ := norm_add_le _ _
      _ ≤ _ := by rw [add_mul]; exact add_le_add h2 h1
  have he := Real.exp_pos (1 / 2 * u)
  calc Real.exp (1 / 2 * u) * ‖Psi2 u + Psi1 u‖
      ≤ Real.exp (1 / 2 * u) * ((2 / Rc ^ 2 + 2 / Rc) * Real.exp (-(5 / 2) * Real.exp (2 * (u - 2 * Rc)))) :=
        mul_le_mul_of_nonneg_left hsum he.le
    _ = (2 / Rc ^ 2 + 2 / Rc) * (Real.exp (1 / 2 * u) * Real.exp (-(5 / 2) * Real.exp (2 * (u - 2 * Rc)))) := by
        ring

/-- **Two-sided bound:** `∃ M, ∀ u, ‖K(u)‖ ≤ M · D_{1/2, 2Rc}(|u|)`. -/
theorem Kker_bound : ∃ M : ℝ, 0 ≤ M ∧ ∀ u : ℝ, ‖Kker u‖ ≤ M * Dabs (1 / 2) (2 * Rc) u := by
  obtain ⟨M₀, hM₀⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 2 * Rc)).exists_bound_of_continuousOn
    continuous_Kker.continuousOn
  have hRc := Rc_pos
  set c₀ : ℝ := Real.exp (-(5 / 2)) with hc₀
  have hc₀pos : 0 < c₀ := Real.exp_pos _
  -- on `[0, 2Rc]`, `D_{1/2}(t) ≥ c₀`
  have hDlow : ∀ t : ℝ, 0 ≤ t → t ≤ 2 * Rc → c₀ ≤ Dprof (1 / 2) (2 * Rc) t := by
    intro t ht0 ht1
    unfold Dprof
    have h1 : 1 ≤ Real.exp (1 / 2 * t) := by
      have := Real.add_one_le_exp (1 / 2 * t)
      linarith [mul_nonneg (by norm_num : (0:ℝ) ≤ 1 / 2) ht0]
    have h2 : c₀ ≤ Real.exp (-(5 / 2) * Real.exp (2 * (t - 2 * Rc))) := by
      apply Real.exp_le_exp.mpr
      have : Real.exp (2 * (t - 2 * Rc)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      nlinarith
    calc c₀ = 1 * c₀ := (one_mul _).symm
      _ ≤ Real.exp (1 / 2 * t) * Real.exp (-(5 / 2) * Real.exp (2 * (t - 2 * Rc))) :=
          mul_le_mul h1 h2 hc₀pos.le (by positivity)
  refine ⟨max (2 / Rc ^ 2 + 2 / Rc) (max M₀ 0 / c₀), le_max_of_le_left (by positivity), fun u => ?_⟩
  rw [Kker_abs]
  have hDnn := Dabs_nonneg (1 / 2) (2 * Rc) u
  rcases le_or_gt |u| (2 * Rc) with hu | hu
  · have hK : ‖Kker |u|‖ ≤ max M₀ 0 := (hM₀ |u| ⟨abs_nonneg u, hu⟩).trans (le_max_left _ _)
    have hD : c₀ ≤ Dabs (1 / 2) (2 * Rc) u := hDlow |u| (abs_nonneg u) hu
    calc ‖Kker |u|‖ ≤ max M₀ 0 := hK
      _ = max M₀ 0 / c₀ * c₀ := by field_simp
      _ ≤ max M₀ 0 / c₀ * Dabs (1 / 2) (2 * Rc) u :=
          mul_le_mul_of_nonneg_left hD (by positivity)
      _ ≤ max (2 / Rc ^ 2 + 2 / Rc) (max M₀ 0 / c₀) * Dabs (1 / 2) (2 * Rc) u :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hDnn
  · calc ‖Kker |u|‖ ≤ (2 / Rc ^ 2 + 2 / Rc) * Dprof (1 / 2) (2 * Rc) |u| := Kker_bound_pos hu.le
      _ = (2 / Rc ^ 2 + 2 / Rc) * Dabs (1 / 2) (2 * Rc) u := rfl
      _ ≤ max (2 / Rc ^ 2 + 2 / Rc) (max M₀ 0 / c₀) * Dabs (1 / 2) (2 * Rc) u :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hDnn

/-! ### The transform and its entireness -/

/-- `Ktrans z = ∫ K(u) e^{izu} du`. -/
noncomputable def Ktrans (z : ℂ) : ℂ := ∫ u : ℝ, Kker u * Complex.exp (I * z * u)

theorem norm_exp_I_mul_le {z : ℂ} {a : ℝ} (ha : |z.im| ≤ a) (u : ℝ) :
    ‖Complex.exp (I * z * u)‖ ≤ Real.exp (a * |u|) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have : (I * z * u).re = -(z.im * u) := by simp [Complex.mul_re, Complex.mul_im]
  rw [this]
  calc -(z.im * u) ≤ |z.im * u| := neg_le_abs _
    _ = |z.im| * |u| := abs_mul _ _
    _ ≤ a * |u| := by gcongr

theorem abs_le_exp_abs (u : ℝ) : |u| ≤ Real.exp |u| := by linarith [Real.add_one_le_exp |u|]

theorem im_le_of_mem_ball {z z₀ : ℂ} (hz : z ∈ Metric.ball z₀ 1) : |z.im| ≤ |z₀.im| + 1 := by
  rw [Metric.mem_ball, Complex.dist_eq] at hz
  have h := Complex.abs_im_le_norm (z - z₀)
  rw [Complex.sub_im] at h
  calc |z.im| = |(z.im - z₀.im) + z₀.im| := by ring_nf
    _ ≤ |z.im - z₀.im| + |z₀.im| := abs_add_le _ _
    _ ≤ 1 + |z₀.im| := by linarith
    _ = |z₀.im| + 1 := by ring

theorem continuous_integrand (z : ℂ) : Continuous (fun u : ℝ => Kker u * Complex.exp (I * z * u)) :=
  continuous_Kker.mul (Complex.continuous_exp.comp (by fun_prop))

theorem continuous_integrand' (z : ℂ) :
    Continuous (fun u : ℝ => Kker u * (I * u * Complex.exp (I * z * u))) :=
  continuous_Kker.mul (by fun_prop)

/-- **`Ktrans` is entire.** -/
theorem hasDerivAt_Ktrans (z₀ : ℂ) :
    HasDerivAt Ktrans (∫ u : ℝ, Kker u * (I * u * Complex.exp (I * z₀ * u))) z₀ := by
  obtain ⟨M, hM, hK⟩ := Kker_bound
  set a : ℝ := |z₀.im| + 1 with ha
  have hball : Metric.ball z₀ 1 ∈ 𝓝 z₀ := Metric.ball_mem_nhds z₀ one_pos
  have hF_meas : ∀ᶠ z in 𝓝 z₀,
      AEStronglyMeasurable (fun u : ℝ => Kker u * Complex.exp (I * z * u)) volume :=
    Eventually.of_forall fun z => (continuous_integrand z).aestronglyMeasurable
  have hF_int : Integrable (fun u : ℝ => Kker u * Complex.exp (I * z₀ * u)) := by
    have hdom : Integrable (fun u : ℝ => M * Dabs (1 / 2 + a) (2 * Rc) u) :=
      (integrable_Dabs (by positivity) _).const_mul M
    refine hdom.mono' (continuous_integrand z₀).aestronglyMeasurable ?_
    filter_upwards with u
    rw [norm_mul]
    calc ‖Kker u‖ * ‖Complex.exp (I * z₀ * u)‖
        ≤ (M * Dabs (1 / 2) (2 * Rc) u) * Real.exp (a * |u|) :=
          mul_le_mul (hK u) (norm_exp_I_mul_le (by rw [ha]; linarith) u) (norm_nonneg _)
            (mul_nonneg hM (Dabs_nonneg _ _ _))
      _ = M * Dabs (1 / 2 + a) (2 * Rc) u := by rw [mul_assoc, Dabs_mul_exp]
  have hF'_meas : AEStronglyMeasurable (fun u : ℝ => Kker u * (I * u * Complex.exp (I * z₀ * u))) volume :=
    (continuous_integrand' z₀).aestronglyMeasurable
  have hbound_int : Integrable (fun u : ℝ => M * Dabs (1 / 2 + (a + 1)) (2 * Rc) u) :=
    (integrable_Dabs (by positivity) _).const_mul M
  have h_bound : ∀ᵐ u ∂volume, ∀ z ∈ Metric.ball z₀ 1,
      ‖Kker u * (I * u * Complex.exp (I * z * u))‖ ≤ M * Dabs (1 / 2 + (a + 1)) (2 * Rc) u := by
    filter_upwards with u
    intro z hz
    have hzim : |z.im| ≤ a := by rw [ha]; exact im_le_of_mem_ball hz
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    calc ‖Kker u‖ * (|u| * ‖Complex.exp (I * z * u)‖)
        ≤ (M * Dabs (1 / 2) (2 * Rc) u) * (Real.exp |u| * Real.exp (a * |u|)) :=
          mul_le_mul (hK u)
            (mul_le_mul (abs_le_exp_abs u) (norm_exp_I_mul_le hzim u) (norm_nonneg _) (Real.exp_pos _).le)
            (by positivity) (mul_nonneg hM (Dabs_nonneg _ _ _))
      _ = (M * Dabs (1 / 2) (2 * Rc) u) * Real.exp ((a + 1) * |u|) := by
          rw [← Real.exp_add]; ring_nf
      _ = M * Dabs (1 / 2 + (a + 1)) (2 * Rc) u := by rw [mul_assoc, Dabs_mul_exp]
  have h_diff : ∀ᵐ u ∂volume, ∀ z ∈ Metric.ball z₀ 1,
      HasDerivAt (fun z : ℂ => Kker u * Complex.exp (I * z * u))
        (Kker u * (I * u * Complex.exp (I * z * u))) z := by
    filter_upwards with u
    intro z _
    have h1 : HasDerivAt (fun z : ℂ => I * z * u) (I * u) z := by
      simpa using ((hasDerivAt_id z).const_mul I).mul_const (u : ℂ)
    exact (h1.cexp.const_mul (Kker u)).congr_deriv (by ring)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hball hF_meas hF_int hF'_meas h_bound
    hbound_int h_diff).2

theorem differentiable_Ktrans : Differentiable ℂ Ktrans := fun z => (hasDerivAt_Ktrans z).differentiableAt

/-! ### Agreement on the half-plane and the identity theorem -/

/-- `ξ(s) = ½ s(s−1) Λ(s)` away from the poles. -/
theorem riemannXi_eq_completed {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    ZD.riemannXi s = s * (s - 1) / 2 * completedRiemannZeta s := by
  unfold ZD.riemannXi
  rw [completedRiemannZeta_eq]
  have h1s : (1 : ℂ) - s ≠ 0 := fun h => hs1 (by linear_combination -h)
  field_simp
  ring

/-- For `Im z < −½`, `Ktrans z = ξ(½ + iz)`. -/
theorem Ktrans_eq_xi_of_lt {z : ℂ} (hz : z.im < -1 / 2) :
    Ktrans z = ZD.riemannXi (1 / 2 + I * z) := by
  set s : ℂ := 1 / 2 + I * z with hsdef
  have hsre : s.re = 1 / 2 - z.im := by simp [hsdef]; ring
  have hs : 1 < s.re := by rw [hsre]; linarith
  have hs0 : s ≠ 0 := fun h => by rw [h] at hsre; simp at hsre; linarith
  have hs1 : s ≠ 1 := fun h => by rw [h] at hsre; simp at hsre; linarith
  rw [riemannXi_eq_completed hs0 hs1, xi_integral_form hs, Ktrans]
  apply integral_congr_ae (Eventually.of_forall fun u => ?_)
  unfold Kker Ew
  rw [show s * (u : ℂ) = (u : ℂ) / 2 + I * z * u by rw [hsdef]; ring, Complex.exp_add]
  ring

theorem differentiable_xiSection : Differentiable ℂ xiSection := by
  have : xiSection = fun z => ZD.riemannXi (1 / 2 + I * z) := rfl
  rw [this]
  exact ZD.riemannXi_differentiable.comp ((differentiable_const _).add ((differentiable_const _).mul differentiable_id))

/-- **T1a: the kernel representation of the ξ-section, for every `z`.** -/
theorem xiSection_eq_Ktrans (z : ℂ) : xiSection z = Ktrans z := by
  have hf : AnalyticOnNhd ℂ xiSection univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr differentiable_xiSection
  have hg : AnalyticOnNhd ℂ Ktrans univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr differentiable_Ktrans
  have hopen : IsOpen {w : ℂ | w.im < -1 / 2} := isOpen_lt Complex.continuous_im continuous_const
  have hmem : (-I : ℂ) ∈ {w : ℂ | w.im < -1 / 2} := by simp; norm_num
  have hev : xiSection =ᶠ[𝓝 (-I)] Ktrans := by
    filter_upwards [hopen.mem_nhds hmem] with w hw
    exact (Ktrans_eq_xi_of_lt hw).symm
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg isPreconnected_univ (mem_univ _) hev (mem_univ z)

end CriticalLinePhasor.XiKernel

#print axioms CriticalLinePhasor.XiKernel.hasDerivAt_Ktrans
#print axioms CriticalLinePhasor.XiKernel.xiSection_eq_Ktrans
