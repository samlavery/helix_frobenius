import RequestProject.CarrierParityQuantization

/-!
# The multiplicity sign law: crossing an event of multiplicity `m` flips the readout by `(-1)^m`

`CarrierParityQuantization` proved that the weld-gauged carrier fiber is real for the exact limit
object.  A real readout carries one bit — its sign — and this file says what that bit counts.  The
statement is local and it is stated **with multiplicity**, which is the point: no simplicity
hypothesis enters anywhere.

## The object

Working in the ordinate variable `z` rather than in `s`, the completed zeta with its two poles
cleared is

`xiEntire z = (½+iz)(½-iz)·Λ₀(½+iz) - 1`,

which is entire (`Λ₀` is entire) and which equals `s(1-s)Λ(s)` at `s = ½+iz` wherever that makes
sense.  On the real axis `s(1-s) = ¼+t²`, strictly positive, so `xiEntire` is real there, vanishes
exactly where `Λ(½+it)` does, and to the same order.  It is the classical Riemann ξ read in the
house's own variable.

## The law

`sign_flip_of_order` is the general statement, for any function analytic at a real point, real on
the real line, not identically zero: the two one-sided values have product of sign `(-1)^m` with
`m` the order of vanishing.  The proof factors `G z = (z-t₀)^m·g z` with `g(t₀) ≠ 0`, observes that
`g` inherits reality along the axis (a punctured-limit argument, since the factor `(t-t₀)^m` is a
nonzero real there), and then reads the sign off `(-h)^m·h^m = (-1)^m h^{2m}`.

`weldReadout_sign_flip` transports it to the carrier readout at every scale `Δ > 0`, the transport
being by two strictly positive factors: `‖weldFactor Δ t‖` and `¼+t²`.  So the sign bit of the
carrier readout flips across an event exactly when the event has odd multiplicity — for every
carrier scale, with nothing assumed about the event.
-/

open Complex Filter Topology

namespace CriticalLinePhasor.CarrierParity

/-- The completed zeta in the ordinate variable, with both poles cleared: `s(1-s)Λ(s)` at
`s = ½+iz`, written so that entirety is manifest. -/
noncomputable def xiEntire (z : ℂ) : ℂ :=
  (1 / 2 + z * I) * (1 / 2 - z * I) * completedRiemannZeta₀ (1 / 2 + z * I) - 1

theorem xiEntire_differentiable : Differentiable ℂ xiEntire := by
  unfold xiEntire
  have hlin : Differentiable ℂ (fun z : ℂ => 1 / 2 + z * I) := by fun_prop
  have hlin' : Differentiable ℂ (fun z : ℂ => 1 / 2 - z * I) := by fun_prop
  exact ((hlin.mul hlin').mul (differentiable_completedZeta₀.comp hlin)).sub
    (differentiable_const _)

theorem xiEntire_analyticOnNhd : AnalyticOnNhd ℂ xiEntire Set.univ :=
  analyticOnNhd_univ_iff_differentiable.mpr xiEntire_differentiable

theorem xiEntire_analyticAt (z : ℂ) : AnalyticAt ℂ xiEntire z :=
  xiEntire_analyticOnNhd z (Set.mem_univ z)

/-- Away from the two poles, `xiEntire` is `s(1-s)Λ(s)`. -/
theorem xiEntire_eq_completed {z : ℂ} (h0 : 1 / 2 + z * I ≠ 0) (h1 : 1 / 2 + z * I ≠ 1) :
    xiEntire z
      = (1 / 2 + z * I) * (1 / 2 - z * I) * completedRiemannZeta (1 / 2 + z * I) := by
  have hsub : (1 : ℂ) - (1 / 2 + z * I) = 1 / 2 - z * I := by ring
  have h1' : (1 : ℂ) / 2 - z * I ≠ 0 := by
    rw [← hsub, sub_ne_zero]; exact fun h => h1 h.symm
  have hsum : (1 / 2 + z * I) + ((1 : ℂ) / 2 - z * I) = 1 := by ring
  -- the pole clearing, with the two factors opaque: `A + B = 1` is the whole of it
  have gen : ∀ A B L : ℂ, A ≠ 0 → B ≠ 0 → A + B = 1 →
      A * B * (L - 1 / A - 1 / B) = A * B * L - 1 := by
    intro A B L hA hB hAB
    have hexp : A * B * (L - 1 / A - 1 / B) = A * B * L - B - A := by field_simp
    rw [hexp]
    linear_combination -hAB
  rw [xiEntire, completedRiemannZeta_eq (1 / 2 + z * I), hsub]
  exact (gen _ _ _ h0 h1' hsum).symm

/-- The line point is never `1`. -/
theorem line_ne_one (t : ℝ) : (1 : ℂ) / 2 + (t : ℂ) * I ≠ 1 := by
  intro h
  have := congrArg Complex.re h
  simp [Complex.add_re, Complex.mul_re] at this

/-- On the real axis `xiEntire` is `(¼+t²)` times the completed zeta: a strictly positive real
multiple, so the two have the same sign and the same zeros with the same orders. -/
theorem xiEntire_ofReal (t : ℝ) :
    xiEntire (t : ℂ)
      = ((1 / 4 + t ^ 2 : ℝ) : ℂ) * completedRiemannZeta (1 / 2 + (t : ℂ) * I) := by
  have hq : (1 / 2 + (t : ℂ) * I) * (1 / 2 - (t : ℂ) * I) = ((1 / 4 + t ^ 2 : ℝ) : ℂ) := by
    push_cast
    linear_combination (-(t : ℂ) ^ 2) * Complex.I_mul_I
  rw [xiEntire_eq_completed (StOscillation.line_ne_zero t) (line_ne_one t), hq]

/-- The clearing factor is strictly positive. -/
theorem quarter_add_sq_pos (t : ℝ) : 0 < 1 / 4 + t ^ 2 := by positivity

/-- `xiEntire` is real on the real axis. -/
theorem xiEntire_im_ofReal (t : ℝ) : (xiEntire (t : ℂ)).im = 0 := by
  rw [xiEntire_ofReal t, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    HelixCollapse.completedRiemannZeta_critical_line_im_zero t]
  ring

/-- The real part of `xiEntire` on the axis. -/
theorem xiEntire_re_ofReal (t : ℝ) :
    (xiEntire (t : ℂ)).re
      = (1 / 4 + t ^ 2) * (completedRiemannZeta (1 / 2 + (t : ℂ) * I)).re := by
  rw [xiEntire_ofReal t, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- `xiEntire` does not vanish identically: at the ordinate `-3i/2`, where `s = 2`. -/
theorem xiEntire_ne_zero_at : xiEntire (-(3 / 2 : ℂ) * I) ≠ 0 := by
  have hs : (1 : ℂ) / 2 + (-(3 / 2 : ℂ) * I) * I = 2 := by
    rw [show (-(3 / 2 : ℂ) * I) * I = -(3 / 2 : ℂ) * (I * I) by ring, Complex.I_mul_I]
    ring
  have hs1 : (1 : ℂ) / 2 - (-(3 / 2 : ℂ) * I) * I = -1 := by
    rw [show (-(3 / 2 : ℂ) * I) * I = -(3 / 2 : ℂ) * (I * I) by ring, Complex.I_mul_I]
    ring
  have h0 : (1 : ℂ) / 2 + (-(3 / 2 : ℂ) * I) * I ≠ 0 := by rw [hs]; norm_num
  have h1 : (1 : ℂ) / 2 + (-(3 / 2 : ℂ) * I) * I ≠ 1 := by rw [hs]; norm_num
  rw [xiEntire_eq_completed h0 h1, hs, hs1]
  have hΛ : completedRiemannZeta (2 : ℂ) ≠ 0 := by
    rw [show completedRiemannZeta (2 : ℂ) = Gammaℝ (2 : ℂ) * riemannZeta (2 : ℂ) by
      rw [riemannZeta_def_of_ne_zero (by norm_num : (2 : ℂ) ≠ 0),
        mul_div_cancel₀ _ (Complex.Gammaℝ_ne_zero_of_re_pos (by norm_num))]]
    exact mul_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos (by norm_num))
      (riemannZeta_ne_zero_of_one_lt_re (by norm_num))
  simpa using hΛ

/-- Hence the order of vanishing is finite at every ordinate. -/
theorem xiEntire_analyticOrderAt_ne_top (z : ℂ) : analyticOrderAt xiEntire z ≠ ⊤ := by
  refine xiEntire_analyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ
    (Set.mem_univ (-(3 / 2 : ℂ) * I)) (Set.mem_univ z) ?_
  have h0 : analyticOrderAt xiEntire (-(3 / 2 : ℂ) * I) = 0 :=
    analyticOrderAt_eq_zero.mpr (Or.inr xiEntire_ne_zero_at)
  exact ne_of_eq_of_ne h0 (by simp)

/-- **The multiplicity sign law, general form.**  Let `G` be analytic at a real point `t₀`, real on
the real axis, and not identically zero near `t₀`.  Then on a punctured real neighbourhood the two
one-sided real parts have product of sign `(-1)^m`, where `m` is the order of vanishing.  Stated
with multiplicity: nothing is assumed about `m`. -/
theorem sign_flip_of_order {G : ℂ → ℂ} {t₀ : ℝ}
    (hG : AnalyticAt ℂ G (t₀ : ℂ))
    (htop : analyticOrderAt G (t₀ : ℂ) ≠ ⊤)
    (hreal : ∀ t : ℝ, (G (t : ℂ)).im = 0) :
    ∃ ε > 0, ∀ h : ℝ, 0 < h → h < ε →
      0 < (-1 : ℝ) ^ (analyticOrderNatAt G (t₀ : ℂ))
            * ((G ((t₀ - h : ℝ) : ℂ)).re * (G ((t₀ + h : ℝ) : ℂ)).re) := by
  set n := analyticOrderNatAt G (t₀ : ℂ) with hn
  obtain ⟨g, hg, hg0, hev⟩ := (hG.analyticOrderNatAt_eq_iff htop).mp rfl
  have hcast : Filter.Tendsto (fun t : ℝ => (t : ℂ)) (nhds t₀) (nhds ((t₀ : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.continuousAt
  have hevR : ∀ᶠ t : ℝ in nhds t₀, G (t : ℂ) = ((t : ℂ) - (t₀ : ℂ)) ^ n • g (t : ℂ) :=
    hcast.eventually hev
  -- the factorization, read on the axis
  have hfac : ∀ t : ℝ, G (t : ℂ) = ((t : ℂ) - (t₀ : ℂ)) ^ n • g (t : ℂ) →
      (G (t : ℂ)).re = (t - t₀) ^ n * (g (t : ℂ)).re := by
    intro t ht
    rw [ht, smul_eq_mul, show ((t : ℂ) - (t₀ : ℂ)) ^ n = (((t - t₀) ^ n : ℝ) : ℂ) from by
      rw [Complex.ofReal_pow, Complex.ofReal_sub], Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im]
    ring
  have hfacIm : ∀ t : ℝ, G (t : ℂ) = ((t : ℂ) - (t₀ : ℂ)) ^ n • g (t : ℂ) →
      (G (t : ℂ)).im = (t - t₀) ^ n * (g (t : ℂ)).im := by
    intro t ht
    rw [ht, smul_eq_mul, show ((t : ℂ) - (t₀ : ℂ)) ^ n = (((t - t₀) ^ n : ℝ) : ℂ) from by
      rw [Complex.ofReal_pow, Complex.ofReal_sub], Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im]
    ring
  -- `g` is real on the punctured axis, hence real at `t₀` by continuity
  have hgIm0 : ∀ᶠ t : ℝ in nhdsWithin t₀ {t₀}ᶜ, (g (t : ℂ)).im = 0 := by
    filter_upwards [hevR.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t ht htne
    have h1 : (t - t₀) ^ n * (g (t : ℂ)).im = 0 := by rw [← hfacIm t ht]; exact hreal t
    have h2 : (t - t₀) ^ n ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr htne)
    exact (mul_eq_zero.mp h1).resolve_left h2
  have hcontIm : ContinuousAt (fun t : ℝ => (g (t : ℂ)).im) t₀ :=
    Complex.continuous_im.continuousAt.comp (hg.continuousAt.comp hcast)
  have him : (g ((t₀ : ℝ) : ℂ)).im = 0 := by
    have hlim : Filter.Tendsto (fun t : ℝ => (g (t : ℂ)).im) (nhdsWithin t₀ {t₀}ᶜ)
        (nhds ((g ((t₀ : ℝ) : ℂ)).im)) := hcontIm.continuousWithinAt
    exact tendsto_nhds_unique hlim
      (Filter.Tendsto.congr' (hgIm0.mono fun t h => h.symm) tendsto_const_nhds)
  have hreNe : (g ((t₀ : ℝ) : ℂ)).re ≠ 0 := fun h => hg0 (Complex.ext h him)
  -- the real part of `g` keeps its sign near `t₀`
  have hcontRe : ContinuousAt (fun t : ℝ => (g ((t₀ : ℝ) : ℂ)).re * (g (t : ℂ)).re) t₀ :=
    continuousAt_const.mul
      (Complex.continuous_re.continuousAt.comp (hg.continuousAt.comp hcast))
  have hpos0 : 0 < (g ((t₀ : ℝ) : ℂ)).re * (g ((t₀ : ℝ) : ℂ)).re :=
    lt_of_le_of_ne (mul_self_nonneg _) (Ne.symm (mul_ne_zero hreNe hreNe))
  have hsign : ∀ᶠ t : ℝ in nhds t₀, 0 < (g ((t₀ : ℝ) : ℂ)).re * (g (t : ℂ)).re :=
    hcontRe.preimage_mem_nhds (Ioi_mem_nhds hpos0)
  -- extract a common radius
  obtain ⟨ε₁, hε₁, H₁⟩ := Metric.eventually_nhds_iff.mp hevR
  obtain ⟨ε₂, hε₂, H₂⟩ := Metric.eventually_nhds_iff.mp hsign
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun h hh hlt => ?_⟩
  have d1 : dist (t₀ - h) t₀ < min ε₁ ε₂ := by
    rw [Real.dist_eq]; simpa [abs_of_pos hh] using hlt
  have d2 : dist (t₀ + h) t₀ < min ε₁ ε₂ := by
    rw [Real.dist_eq]; simpa [abs_of_pos hh] using hlt
  have e1 := hfac (t₀ - h) (H₁ (lt_of_lt_of_le d1 (min_le_left _ _)))
  have e2 := hfac (t₀ + h) (H₁ (lt_of_lt_of_le d2 (min_le_left _ _)))
  have s1 := H₂ (lt_of_lt_of_le d1 (min_le_right _ _))
  have s2 := H₂ (lt_of_lt_of_le d2 (min_le_right _ _))
  rw [e1, e2]
  have hgg : 0 < (g (((t₀ - h : ℝ)) : ℂ)).re * (g (((t₀ + h : ℝ)) : ℂ)).re := by
    have h3 : 0 < ((g ((t₀ : ℝ) : ℂ)).re * (g (((t₀ - h : ℝ)) : ℂ)).re)
        * ((g ((t₀ : ℝ) : ℂ)).re * (g (((t₀ + h : ℝ)) : ℂ)).re) := mul_pos s1 s2
    have h4 : ((g ((t₀ : ℝ) : ℂ)).re * (g (((t₀ - h : ℝ)) : ℂ)).re)
        * ((g ((t₀ : ℝ) : ℂ)).re * (g (((t₀ + h : ℝ)) : ℂ)).re)
        = ((g ((t₀ : ℝ) : ℂ)).re * (g ((t₀ : ℝ) : ℂ)).re)
          * ((g (((t₀ - h : ℝ)) : ℂ)).re * (g (((t₀ + h : ℝ)) : ℂ)).re) := by ring
    rw [h4] at h3
    exact (mul_pos_iff_of_pos_left hpos0).mp h3
  have hsq : (-1 : ℝ) ^ n * (-1 : ℝ) ^ n = 1 := by rw [← mul_pow]; norm_num
  have hh2 : (0 : ℝ) < h ^ n * h ^ n := by positivity
  have key : (-1 : ℝ) ^ n * ((((t₀ - h) - t₀) ^ n * (g (((t₀ - h : ℝ)) : ℂ)).re)
        * ((((t₀ + h) - t₀) ^ n) * (g (((t₀ + h : ℝ)) : ℂ)).re))
      = ((-1 : ℝ) ^ n * (-1 : ℝ) ^ n) * ((h ^ n * h ^ n)
          * ((g (((t₀ - h : ℝ)) : ℂ)).re * (g (((t₀ + h : ℝ)) : ℂ)).re)) := by
    rw [show (t₀ - h) - t₀ = -h from by ring, show (t₀ + h) - t₀ = h from by ring, neg_pow]
    ring
  rw [key, hsq, one_mul]
  exact mul_pos hh2 hgg

/-- **The multiplicity sign law at the events.**  Crossing an event of multiplicity `m` multiplies
the weld-gauged carrier readout by `(-1)^m`, at every carrier scale `Δ > 0`.  Stated with
multiplicity, so no simplicity hypothesis enters — the law is the same for a double zero as for a
simple one, and it is the even case that leaves the bit unchanged. -/
theorem weldReadout_sign_flip {Δ : ℝ} (hΔ : 0 < Δ) (t₀ : ℝ) :
    ∃ ε > 0, ∀ h : ℝ, 0 < h → h < ε →
      0 < (-1 : ℝ) ^ (analyticOrderNatAt xiEntire (t₀ : ℂ))
            * (weldReadout Δ (t₀ - h) * weldReadout Δ (t₀ + h)) := by
  obtain ⟨ε, hε, H⟩ := sign_flip_of_order (xiEntire_analyticAt (t₀ : ℂ))
    (xiEntire_analyticOrderAt_ne_top _) xiEntire_im_ofReal
  refine ⟨ε, hε, fun h hh hlt => ?_⟩
  have key := H h hh hlt
  rw [xiEntire_re_ofReal, xiEntire_re_ofReal] at key
  have p1 : 0 < ‖weldFactor Δ (t₀ - h)‖ := norm_pos_iff.mpr (weldFactor_ne_zero hΔ _)
  have p2 : 0 < ‖weldFactor Δ (t₀ + h)‖ := norm_pos_iff.mpr (weldFactor_ne_zero hΔ _)
  have q1 := quarter_add_sq_pos (t₀ - h)
  have q2 := quarter_add_sq_pos (t₀ + h)
  have hexpand : weldReadout Δ (t₀ - h) * weldReadout Δ (t₀ + h)
      = (‖weldFactor Δ (t₀ - h)‖ * ‖weldFactor Δ (t₀ + h)‖
          / ((1 / 4 + (t₀ - h) ^ 2) * (1 / 4 + (t₀ + h) ^ 2)))
        * (((1 / 4 + (t₀ - h) ^ 2) * (completedRiemannZeta (1 / 2 + ((t₀ - h : ℝ) : ℂ) * I)).re)
          * ((1 / 4 + (t₀ + h) ^ 2)
              * (completedRiemannZeta (1 / 2 + ((t₀ + h : ℝ) : ℂ) * I)).re)) := by
    rw [weldReadout, weldReadout]
    field_simp
  rw [hexpand, ← mul_assoc, mul_comm ((-1 : ℝ) ^ _), mul_assoc]
  exact mul_pos (div_pos (mul_pos p1 p2) (mul_pos q1 q2)) key

end CriticalLinePhasor.CarrierParity
