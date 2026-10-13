import RequestProject.AreaDilation

/-!
# The Hilbert–Pólya step in dilation form (ledger 1220)

A Mellin evaluation intertwines the area-measure dilation `V_t` with the scalar `e^{t(½ − s)}`
(`AreaDilation.dil_power`, dually). This file isolates the step that turns such covariance into the
critical line.

* `covariant_functional_re`: on a normed space with dilation operators `V_t` whose norms grow
  subexponentially (`‖V_t x‖ ≤ B(|t|)·‖x‖`, `B(u)/e^{cu} → 0` for every `c > 0`; isometries and
  polynomial growth included), a NONZERO CONTINUOUS linear functional with
  `φ ∘ V_t = e^{t(½ − s)}·φ` for all `t` has `Re s = ½`.
* `covariant_functional_re_of_isometry`: the isometric case.

So, for a zero `ρ`, the critical-line conclusion follows exactly when its Mellin functional is CONTINUOUS
on a space where the dilations grow subexponentially. Whether that holds for every zero is the
remaining question; it is not assumed here.
-/

open Complex Filter Topology

noncomputable section

namespace CriticalLinePhasor.DilationEigen

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- **Covariance under subexponentially bounded dilations forces `Re s = ½`.** -/
theorem covariant_functional_re (V : ℝ → X →L[ℂ] X) (B : ℝ → ℝ)
    (hV : ∀ t x, ‖V t x‖ ≤ B |t| * ‖x‖)
    (hB : ∀ c : ℝ, 0 < c → Tendsto (fun u => B u / Real.exp (c * u)) atTop (𝓝 0))
    (φ : X →L[ℂ] ℂ) (hφ : φ ≠ 0) (s : ℂ)
    (hcov : ∀ t x, φ (V t x) = Complex.exp ((t : ℂ) * (1 / 2 - s)) * φ x) : s.re = 1 / 2 := by
  obtain ⟨x, hx⟩ : ∃ x, φ x ≠ 0 := by
    by_contra h
    exact hφ (ContinuousLinearMap.ext fun y => by simpa using (not_exists.mp h y))
  have hbound : ∀ t : ℝ, Real.exp (t * (1 / 2 - s.re)) * ‖φ x‖ ≤ ‖φ‖ * (B |t| * ‖x‖) := by
    intro t
    have h1 : ‖φ (V t x)‖ ≤ ‖φ‖ * ‖V t x‖ := φ.le_opNorm _
    rw [hcov, norm_mul, Complex.norm_exp] at h1
    have hre : ((t : ℂ) * (1 / 2 - s)).re = t * (1 / 2 - s.re) := by simp
    rw [hre] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left (hV t x) (norm_nonneg _))
  have hpos : 0 < ‖φ x‖ := norm_pos_iff.mpr hx
  by_contra hne
  set c := |1 / 2 - s.re| with hcdef
  have hc : 0 < c := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hne))
  have hb' : ∀ u : ℝ, 0 ≤ u → Real.exp (c * u) * ‖φ x‖ ≤ ‖φ‖ * (B u * ‖x‖) := by
    intro u hu
    rcases le_or_gt 0 (1 / 2 - s.re) with h | h
    · have := hbound u
      rw [abs_of_nonneg hu] at this
      rwa [hcdef, abs_of_nonneg h, mul_comm (1 / 2 - s.re)]
    · have := hbound (-u)
      rw [abs_neg, abs_of_nonneg hu, show -u * (1 / 2 - s.re) = (-(1 / 2 - s.re)) * u by ring]
        at this
      rwa [hcdef, abs_of_neg h]
  -- ‖φ x‖ ≤ ‖φ‖‖x‖·B(u)/e^{cu} → 0
  have hlim := ((hB c hc).const_mul (‖φ‖ * ‖x‖))
  rw [mul_zero] at hlim
  have hev := hlim.eventually (gt_mem_nhds hpos)
  obtain ⟨u, hu1, hu0⟩ := (hev.and (eventually_ge_atTop (0 : ℝ))).exists
  have hb := hb' u hu0
  have hE : 0 < Real.exp (c * u) := Real.exp_pos _
  have : ‖φ x‖ ≤ ‖φ‖ * ‖x‖ * (B u / Real.exp (c * u)) := by
    rw [mul_div_assoc', le_div_iff₀ hE]
    nlinarith [hb]
  linarith

/-- **The isometric case.** -/
theorem covariant_functional_re_of_isometry (V : ℝ → X →L[ℂ] X) (hV : ∀ t x, ‖V t x‖ = ‖x‖)
    (φ : X →L[ℂ] ℂ) (hφ : φ ≠ 0) (s : ℂ)
    (hcov : ∀ t x, φ (V t x) = Complex.exp ((t : ℂ) * (1 / 2 - s)) * φ x) : s.re = 1 / 2 := by
  refine covariant_functional_re V (fun _ => 1) (fun t x => by rw [hV, one_mul]) ?_ φ hφ s hcov
  intro c hc
  have h := (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hc)).inv_tendsto_atTop
  simp only [one_div]
  exact h

end CriticalLinePhasor.DilationEigen

end

#print axioms CriticalLinePhasor.DilationEigen.covariant_functional_re
#print axioms CriticalLinePhasor.DilationEigen.covariant_functional_re_of_isometry
