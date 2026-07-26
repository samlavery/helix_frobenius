import RequestProject.RiemannXiDecay

/-!
# Vertical-line integrability of the complex Γ-factor (from house Stirling)

The unconditional two-sided Stirling bound `ZD.StirlingBound.gamma_stirling_bound` gives, on every
vertical line `Re s = σ > 0`, exponential decay `‖Γ(σ+it)‖ ≤ C·|t|^{σ-1/2}·e^{-π|t|/2}` for
`|t|` large.  Polynomial × exponential is integrable, so `Γ` — and hence Deligne's `Γ_ℂ` — is
integrable along any vertical line in the right half-plane.  This is the analytic fact behind the
`VerticalIntegrable` side conditions of the Mellin-inversion coupling converter: it is **not** a
Mathlib boundary, the bound lives in `StirlingBound.lean`.

* `gammaC_vertical_isBigO_atTop` / `_atBot` — the Stirling exponential decay repackaged as
  `IsBigO` against `e^{∓(π/4)y}`.
* `gammaC_vertical_integrable` — `Integrable (fun y => Γ_ℂ(w + iy))` for `0 < w.re`.

No RH/GRH.
-/

open Complex Filter Topology Asymptotics MeasureTheory Real

namespace CriticalLinePhasor.GammaVertical

/-- The complex point `w + iy`. -/
noncomputable def vline (w : ℂ) (y : ℝ) : ℂ := w + (y : ℂ) * Complex.I

/-- A shifted vertical-line argument is a vertical line about the shifted base point. -/
theorem vline_add (w c : ℂ) (y : ℝ) : w + (y : ℂ) * Complex.I + c = vline (w + c) y := by
  unfold vline; ring

theorem vline_baseAdd (σ : ℝ) (μ : ℂ) (y : ℝ) :
    (σ : ℂ) + (y : ℂ) * Complex.I + μ = vline ((σ : ℂ) + μ) y := by
  unfold vline; ring

private theorem vline_re (w : ℂ) (y : ℝ) : (vline w y).re = w.re := by
  simp [vline]

private theorem vline_im (w : ℂ) (y : ℝ) : (vline w y).im = w.im + y := by
  simp [vline]

/-- `w + iy` as the pair `⟨w.re, w.im + y⟩`. -/
private theorem vline_eq_mk (w : ℂ) (y : ℝ) :
    vline w y = (⟨w.re, w.im + y⟩ : ℂ) := by
  apply Complex.ext <;> simp [vline_re, vline_im]

/-- Continuity of the Γ-factor along a vertical line strictly inside the right half-plane. -/
theorem gammaC_vline_continuous {w : ℂ} (hw : 0 < w.re) :
    Continuous (fun y : ℝ => Complex.Gammaℂ (vline w y)) := by
  have hne : ∀ y : ℝ, ∀ m : ℕ, vline w y ≠ -m := by
    intro y m h
    have : (vline w y).re = -(m : ℝ) := by rw [h]; simp
    rw [vline_re] at this
    have : (0:ℝ) < -(m:ℝ) := this ▸ hw
    have hm : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
    linarith
  have hlineCont : Continuous (fun y : ℝ => vline w y) := by
    unfold vline; fun_prop
  have hgammaDiff : ∀ y : ℝ, DifferentiableAt ℂ Complex.Gamma (vline w y) := by
    intro y; exact Complex.differentiableAt_Gamma _ (hne y)
  -- Γ_ℂ s = 2 * (2π)^(-s) * Γ s
  have hunfold : (fun y : ℝ => Complex.Gammaℂ (vline w y)) =
      fun y : ℝ => 2 * (2 * (Real.pi : ℂ)) ^ (-(vline w y)) * Complex.Gamma (vline w y) := by
    funext y; rw [Complex.Gammaℂ_def]
  rw [hunfold]
  have h2pi_ne : (2 * (Real.pi : ℂ)) ≠ 0 := by
    have hne : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    simpa using mul_ne_zero (two_ne_zero) hne
  have hcpow : Continuous (fun y : ℝ => (2 * (Real.pi : ℂ)) ^ (-(vline w y))) :=
    (hlineCont.neg).const_cpow (Or.inl h2pi_ne)
  have hgammaCont : Continuous (fun y : ℝ => Complex.Gamma (vline w y)) :=
    continuous_iff_continuousAt.mpr fun y =>
      (hgammaDiff y).continuousAt.comp hlineCont.continuousAt
  fun_prop

/-- The Γ_ℂ norm on a vertical line is a constant times the Γ norm. -/
theorem gammaC_vline_norm (w : ℂ) (y : ℝ) :
    ‖Complex.Gammaℂ (vline w y)‖ =
      2 * (2 * Real.pi) ^ (-w.re) * ‖Complex.Gamma (vline w y)‖ := by
  rw [Complex.Gammaℂ_def, norm_mul, norm_mul]
  have hbase : (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; ring
  have h2pi : (0:ℝ) < 2 * Real.pi := by positivity
  rw [hbase, Complex.norm_cpow_eq_rpow_re_of_pos h2pi]
  have hre : (-(vline w y)).re = -w.re := by rw [Complex.neg_re, vline_re]
  rw [hre]
  norm_num

/-- The Stirling exponential decay of Γ_ℂ, repackaged as `IsBigO` at `+∞`. -/
theorem gammaC_vline_isBigO_atTop {w : ℂ} (hw : 0 < w.re) :
    (fun y : ℝ => Complex.Gammaℂ (vline w y)) =O[atTop]
      fun y => Real.exp (-(Real.pi / 4) * y) := by
  set p : ℝ := w.re - 1 / 2 with hp
  set K : ℝ := 2 * (2 * Real.pi) ^ (-w.re) with hK
  have hKpos : 0 < K := by rw [hK]; positivity
  obtain ⟨_C_lo, C_hi, T₀, _hClo, hChi, hT0, hbnd⟩ :=
    ZD.StirlingBound.gamma_stirling_bound w.re hw
  rw [← hp] at hbnd
  -- (a) ‖Γ_ℂ(vline)‖ =O[atTop] g₁ where g₁ y = |w.im+y|^p · exp(-π|w.im+y|/2)
  set g₁ : ℝ → ℝ := fun y => |w.im + y| ^ p * Real.exp (-Real.pi * |w.im + y| / 2) with hg1
  have hOa : (fun y : ℝ => Complex.Gammaℂ (vline w y)) =O[atTop] g₁ := by
    rw [isBigO_iff]
    refine ⟨K * C_hi, ?_⟩
    have hev : ∀ᶠ y : ℝ in atTop, T₀ ≤ |w.im + y| := by
      have hten : Tendsto (fun y : ℝ => |w.im + y|) atTop atTop :=
        tendsto_abs_atTop_atTop.comp (tendsto_atTop_add_const_left _ _ tendsto_id)
      exact hten.eventually_ge_atTop T₀
    filter_upwards [hev] with y hy
    have hstir := (hbnd (w.im + y) hy).2
    rw [← vline_eq_mk w y] at hstir
    rw [gammaC_vline_norm w y]
    have hg1nn : 0 ≤ g₁ y := by rw [hg1]; positivity
    calc 2 * (2 * Real.pi) ^ (-w.re) * ‖Complex.Gamma (vline w y)‖
        ≤ K * (C_hi * |w.im + y| ^ p * Real.exp (-Real.pi * |w.im + y| / 2)) := by
          rw [hK]; exact mul_le_mul_of_nonneg_left hstir (by positivity)
      _ = (K * C_hi) * g₁ y := by rw [hg1]; ring
      _ = K * C_hi * ‖g₁ y‖ := by rw [Real.norm_eq_abs, abs_of_nonneg hg1nn]
  -- (b) g₁ =o[atTop] exp(-(π/4)·)
  have hOb : g₁ =o[atTop] fun y => Real.exp (-(Real.pi / 4) * y) := by
    have hpi4 : (0:ℝ) < Real.pi / 4 := by positivity
    have htend0 : Tendsto (fun u : ℝ => u ^ p * Real.exp (-(Real.pi / 4) * u))
        atTop (𝓝 0) := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero p (Real.pi / 4) hpi4
    have hshift : Tendsto (fun y : ℝ => w.im + y) atTop atTop :=
      tendsto_atTop_add_const_left _ _ tendsto_id
    have htend : Tendsto
        (fun y : ℝ => Real.exp (-(Real.pi * w.im) / 4) *
          ((w.im + y) ^ p * Real.exp (-(Real.pi / 4) * (w.im + y)))) atTop (𝓝 0) := by
      have h := (htend0.comp hshift).const_mul (Real.exp (-(Real.pi * w.im) / 4))
      simp only [mul_zero] at h
      exact h
    refine Asymptotics.isLittleO_of_tendsto
      (fun x hx => absurd hx (Real.exp_ne_zero _)) ?_
    refine htend.congr' ?_
    filter_upwards [eventually_ge_atTop (-w.im)] with y hy
    have hpos : 0 ≤ w.im + y := by linarith
    show Real.exp (-(Real.pi * w.im) / 4) *
        ((w.im + y) ^ p * Real.exp (-(Real.pi / 4) * (w.im + y))) =
      g₁ y / Real.exp (-(Real.pi / 4) * y)
    rw [hg1]
    simp only
    rw [abs_of_nonneg hpos]
    have hL : Real.exp (-(Real.pi * w.im) / 4) *
        ((w.im + y) ^ p * Real.exp (-(Real.pi / 4) * (w.im + y))) =
        (w.im + y) ^ p *
          Real.exp (-(Real.pi * w.im) / 4 + -(Real.pi / 4) * (w.im + y)) := by
      rw [Real.exp_add]; ring
    have hR : (w.im + y) ^ p * Real.exp (-Real.pi * (w.im + y) / 2) /
        Real.exp (-(Real.pi / 4) * y) =
        (w.im + y) ^ p *
          Real.exp (-Real.pi * (w.im + y) / 2 - -(Real.pi / 4) * y) := by
      rw [Real.exp_sub]; ring
    rw [hL, hR]
    congr 1
    rw [show -(Real.pi * w.im) / 4 + -(Real.pi / 4) * (w.im + y) =
      -Real.pi * (w.im + y) / 2 - -(Real.pi / 4) * y from by ring]
  exact (hOa.trans_isLittleO hOb).isBigO

/-- The Stirling exponential decay of Γ_ℂ, repackaged as `IsBigO` at `-∞`. -/
theorem gammaC_vline_isBigO_atBot {w : ℂ} (hw : 0 < w.re) :
    (fun y : ℝ => Complex.Gammaℂ (vline w y)) =O[atBot]
      fun y => Real.exp (Real.pi / 4 * y) := by
  set p : ℝ := w.re - 1 / 2 with hp
  set K : ℝ := 2 * (2 * Real.pi) ^ (-w.re) with hK
  have hKpos : 0 < K := by rw [hK]; positivity
  obtain ⟨_C_lo, C_hi, T₀, _hClo, hChi, hT0, hbnd⟩ :=
    ZD.StirlingBound.gamma_stirling_bound w.re hw
  rw [← hp] at hbnd
  set g₁ : ℝ → ℝ := fun y => |w.im + y| ^ p * Real.exp (-Real.pi * |w.im + y| / 2) with hg1
  have hOa : (fun y : ℝ => Complex.Gammaℂ (vline w y)) =O[atBot] g₁ := by
    rw [isBigO_iff]
    refine ⟨K * C_hi, ?_⟩
    have hev : ∀ᶠ y : ℝ in atBot, T₀ ≤ |w.im + y| := by
      have hten : Tendsto (fun y : ℝ => |w.im + y|) atBot atTop :=
        tendsto_abs_atBot_atTop.comp (tendsto_atBot_add_const_left _ _ tendsto_id)
      exact hten.eventually_ge_atTop T₀
    filter_upwards [hev] with y hy
    have hstir := (hbnd (w.im + y) hy).2
    rw [← vline_eq_mk w y] at hstir
    rw [gammaC_vline_norm w y]
    have hg1nn : 0 ≤ g₁ y := by rw [hg1]; positivity
    calc 2 * (2 * Real.pi) ^ (-w.re) * ‖Complex.Gamma (vline w y)‖
        ≤ K * (C_hi * |w.im + y| ^ p * Real.exp (-Real.pi * |w.im + y| / 2)) := by
          rw [hK]; exact mul_le_mul_of_nonneg_left hstir (by positivity)
      _ = (K * C_hi) * g₁ y := by rw [hg1]; ring
      _ = K * C_hi * ‖g₁ y‖ := by rw [Real.norm_eq_abs, abs_of_nonneg hg1nn]
  have hOb : g₁ =o[atBot] fun y => Real.exp (Real.pi / 4 * y) := by
    have hpi4 : (0:ℝ) < Real.pi / 4 := by positivity
    have htend0 : Tendsto (fun u : ℝ => u ^ p * Real.exp (-(Real.pi / 4) * u))
        atTop (𝓝 0) := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero p (Real.pi / 4) hpi4
    have hshift : Tendsto (fun y : ℝ => -(w.im + y)) atBot atTop := by
      have : Tendsto (fun y : ℝ => w.im + y) atBot atBot :=
        tendsto_atBot_add_const_left _ _ tendsto_id
      exact tendsto_neg_atBot_atTop.comp this
    have htend : Tendsto
        (fun y : ℝ => Real.exp (Real.pi / 4 * w.im) *
          ((-(w.im + y)) ^ p * Real.exp (-(Real.pi / 4) * (-(w.im + y))))) atBot (𝓝 0) := by
      have h := (htend0.comp hshift).const_mul (Real.exp (Real.pi / 4 * w.im))
      simpa using h
    refine Asymptotics.isLittleO_of_tendsto
      (fun x hx => absurd hx (Real.exp_ne_zero _)) ?_
    refine htend.congr' ?_
    filter_upwards [eventually_le_atBot (-w.im)] with y hy
    have hnp : w.im + y ≤ 0 := by linarith
    show Real.exp (Real.pi / 4 * w.im) *
        ((-(w.im + y)) ^ p * Real.exp (-(Real.pi / 4) * (-(w.im + y)))) =
      g₁ y / Real.exp (Real.pi / 4 * y)
    rw [hg1]
    simp only
    rw [abs_of_nonpos hnp]
    have hL : Real.exp (Real.pi / 4 * w.im) *
        ((-(w.im + y)) ^ p * Real.exp (-(Real.pi / 4) * (-(w.im + y)))) =
        (-(w.im + y)) ^ p *
          Real.exp (Real.pi / 4 * w.im + -(Real.pi / 4) * (-(w.im + y))) := by
      rw [Real.exp_add]; ring
    have hR : (-(w.im + y)) ^ p * Real.exp (-Real.pi * (-(w.im + y)) / 2) /
        Real.exp (Real.pi / 4 * y) =
        (-(w.im + y)) ^ p *
          Real.exp (-Real.pi * (-(w.im + y)) / 2 - Real.pi / 4 * y) := by
      rw [Real.exp_sub]; ring
    rw [hL, hR]
    congr 1
    rw [show Real.pi / 4 * w.im + -(Real.pi / 4) * (-(w.im + y)) =
      -Real.pi * (-(w.im + y)) / 2 - Real.pi / 4 * y from by ring]
  exact (hOa.trans_isLittleO hOb).isBigO

/-- **Γ_ℂ is integrable on every vertical line in the right half-plane.**  Continuity plus the
two-sided Stirling exponential decay give integrability at both ends. -/
theorem gammaC_vline_integrable {w : ℂ} (hw : 0 < w.re) :
    Integrable (fun y : ℝ => Complex.Gammaℂ (vline w y)) := by
  have hpi4 : (0:ℝ) < Real.pi / 4 := by positivity
  have hcont := gammaC_vline_continuous hw
  refine (hcont.locallyIntegrable).integrable_of_isBigO_atBot_atTop
    (gammaC_vline_isBigO_atBot hw) ?_ (gammaC_vline_isBigO_atTop hw) ?_
  · -- IntegrableAtFilter (exp((π/4)·)) atBot
    refine ⟨Set.Iio 0, Iio_mem_atBot 0, ?_⟩
    have hpre : (Neg.neg : ℝ → ℝ) ⁻¹' (Set.Iio 0) = Set.Ioi 0 := by
      ext y; simp
    have hfun : (fun y : ℝ => Real.exp (Real.pi / 4 * y)) ∘ (Neg.neg : ℝ → ℝ)
        = fun y : ℝ => Real.exp (-(Real.pi / 4) * y) := by
      funext y; simp only [Function.comp_apply]; ring_nf
    refine ((Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
      measurableEmbedding_neg (f := fun y : ℝ => Real.exp (Real.pi / 4 * y))
      (s := Set.Iio 0)).mp ?_
    rw [hpre, hfun]
    exact exp_neg_integrableOn_Ioi 0 hpi4
  · -- IntegrableAtFilter (exp(-(π/4)·)) atTop
    exact ⟨Set.Ioi 0, Ioi_mem_atTop 0, exp_neg_integrableOn_Ioi 0 hpi4⟩

end CriticalLinePhasor.GammaVertical

#print axioms CriticalLinePhasor.GammaVertical.gammaC_vline_continuous
#print axioms CriticalLinePhasor.GammaVertical.gammaC_vline_isBigO_atTop
#print axioms CriticalLinePhasor.GammaVertical.gammaC_vline_isBigO_atBot
#print axioms CriticalLinePhasor.GammaVertical.gammaC_vline_integrable
