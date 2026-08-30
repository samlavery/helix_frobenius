import c3b6_A3

/-!
# C3 batch 6, block A4 — `K_{ix}(A) > 0` above an explicit threshold, and the
unconditional radial positivity

Block A3 left exactly one hypothesis on `radial_kix_pos`: positivity of `K_{ix}` on the
ray.  This file discharges it with an **explicit, unconditional threshold**, by the
first-lobe estimate:

with `h := 1/(|x|+1)` and `M := e^{-A cosh h}`,

* on `(0,h]` the phase is inside the first lobe (`|xw| ≤ |x|h < 1`), so
  `cos(xw) ≥ 1 − (xw)²/2 ≥ ½`, and `e^{-A cosh w} ≥ M`.  Hence the head is `≥ M·h/2`.
* on `(h,∞)` convexity of `cosh` gives `cosh w ≥ cosh h + sinh h·(w−h)`, so the tail is
  `≤ M/(A sinh h)` — the whole tail, with the exponential rate strictly separated from the
  head's by the *linear* term, which is what makes the comparison `A`-sensitive.
* `sinh h ≥ h/2` for `h ≥ 0`, so `A·h·sinh h ≥ A h²/2 > 2` as soon as `A > 4/h²`.

Result: **`K_{ix}(A) > 0` for every `A > 4(|x|+1)²`.**

This is quadratic in `x` where the true turning point is linear (`A > √(x²+¼)`), so the
compact window it leaves is `[0, ½log(4(x+1)²/2π)]` rather than `[0, ½log(x/2π)]`.  The
gap is the price of a proof that uses only convexity of `cosh` and the first lobe; it is
recorded as such, not hidden.

`radial_kix_pos_uncond` is then the **hypothesis-free** form of obligation A: for
`a ≥ max(8, 4(|x|+1)²)`, `0 < (A²+9)K_{ix}(A) + 6A·K′_{ix}(A)` on `[a,∞)`.

SCOPE: nothing here mentions `Ξ`, zeros, or RH.
-/

open MeasureTheory Set Filter Topology

noncomputable section

namespace C3B6.Bessel

/-! ### 0. Shape of the order-zero integrand -/

theorem kixTerm_zero_eq (x A w : ℝ) :
    kixTerm 0 x A w = Real.exp (-(A * Real.cosh w)) * Real.cos (x * w) := by
  unfold kixTerm; rw [pow_zero, one_mul]

/-! ### 1. Hyperbolic comparisons -/

theorem cosh_le_cosh_of_le {w h : ℝ} (hw : 0 ≤ w) (hwh : w ≤ h) :
    Real.cosh w ≤ Real.cosh h := by
  have h1 : Real.sinh w ≤ Real.sinh h := Real.sinh_le_sinh.mpr hwh
  have h2 : 0 ≤ Real.sinh w := Real.sinh_nonneg_iff.mpr hw
  have e1 := Real.cosh_sq_sub_sinh_sq w
  have e2 := Real.cosh_sq_sub_sinh_sq h
  have p1 := Real.cosh_pos w
  have p2 := Real.cosh_pos h
  nlinarith

/-- **`sinh h ≥ h/2` for `h ≥ 0`.**  Elementary, from `e^h ≥ 1+h`. -/
theorem half_le_sinh {h : ℝ} (hh : 0 ≤ h) : h / 2 ≤ Real.sinh h := by
  have hp : (1 : ℝ) + h ≤ Real.exp h := by
    have := Real.add_one_le_exp h
    linarith
  have hpos : (0 : ℝ) < Real.exp h := Real.exp_pos h
  have hinv : Real.exp (-h) = (Real.exp h)⁻¹ := Real.exp_neg h
  have hprod : Real.exp h * Real.exp (-h) = 1 := by
    rw [← Real.exp_add]; simp
  rw [Real.sinh_eq]
  have hkey : h * Real.exp h ≤ Real.exp h * Real.exp h - 1 := by
    nlinarith [hp, hh, hpos]
  have hstep : h * Real.exp h ≤ Real.exp h * Real.exp h - Real.exp h * Real.exp (-h) := by
    rw [hprod]; exact hkey
  nlinarith [hstep, hpos]

/-- **The tangent-line lower bound for `cosh`.**  `cosh w ≥ cosh h + sinh h·(w−h)` for
`w ≥ h ≥ 0`.  This is what separates the tail's exponential rate from the head's. -/
theorem cosh_tangent_lower {h w : ℝ} (hh : 0 ≤ h) (hw : h ≤ w) :
    Real.cosh h + Real.sinh h * (w - h) ≤ Real.cosh w := by
  have hF : ∀ t : ℝ, HasDerivAt
      (fun s : ℝ => Real.cosh s - Real.cosh h - Real.sinh h * (s - h))
      (Real.sinh t - Real.sinh h) t := by
    intro t
    have h1 := Real.hasDerivAt_cosh t
    have h2 : HasDerivAt (fun s : ℝ => Real.sinh h * (s - h)) (Real.sinh h) t := by
      have h3 : HasDerivAt (fun s : ℝ => s - h) (1 : ℝ) t :=
        (hasDerivAt_id' (x := t)).sub_const h
      have := h3.const_mul (Real.sinh h)
      refine this.congr_deriv ?_
      ring
    have := (h1.sub_const (Real.cosh h)).sub h2
    exact this
  have hmono : MonotoneOn
      (fun s : ℝ => Real.cosh s - Real.cosh h - Real.sinh h * (s - h)) (Ici h) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici h) ?_ ?_ ?_
    · exact fun t _ => ((hF t).continuousAt).continuousWithinAt
    · intro t _
      exact ((hF t).differentiableAt).differentiableWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      rw [(hF t).deriv]
      have : Real.sinh h ≤ Real.sinh t := Real.sinh_le_sinh.mpr (le_of_lt ht)
      linarith
  have hstep := hmono (mem_Ici.mpr (le_refl h)) (mem_Ici.mpr hw) hw
  simp only [sub_self, mul_zero] at hstep
  linarith

/-! ### 2. The exponential tail integral -/

theorem integral_exp_neg_shift {c h : ℝ} (hc : 0 < c) :
    (∫ w in Ioi h, Real.exp (-(c * (w - h)))) = 1 / c := by
  have hfun : (fun w : ℝ => Real.exp (-(c * (w - h))))
      = fun w : ℝ => Real.exp (c * h) * Real.exp (-c * w) := by
    funext w
    rw [← Real.exp_add]
    congr 1
    ring
  have hint : IntegrableOn (fun w : ℝ => Real.exp (-(c * (w - h)))) (Ioi h) := by
    rw [hfun]
    exact (exp_neg_integrableOn_Ioi h hc).const_mul _
  have hderiv : ∀ w ∈ Ici h,
      HasDerivAt (fun t : ℝ => -(1 / c) * Real.exp (-(c * (t - h))))
        (Real.exp (-(c * (w - h)))) w := by
    intro w _
    have h3 : HasDerivAt (fun s : ℝ => s - h) (1 : ℝ) w :=
      (hasDerivAt_id' (x := w)).sub_const h
    have h4 : HasDerivAt (fun s : ℝ => -(c * (s - h))) (-c) w := by
      have := (h3.const_mul c).neg
      refine this.congr_deriv ?_
      ring
    have hexp := h4.exp
    have h5 := hexp.const_mul (-(1 / c))
    refine h5.congr_deriv ?_
    field_simp
  have hlim : Tendsto (fun t : ℝ => -(1 / c) * Real.exp (-(c * (t - h)))) atTop (nhds 0) := by
    have h1 : Tendsto (fun t : ℝ => t - h) atTop atTop :=
      tendsto_atTop_add_const_right atTop (-h) tendsto_id
    have h2 : Tendsto (fun t : ℝ => c * (t - h)) atTop atTop :=
      Filter.Tendsto.const_mul_atTop hc h1
    have h3 : Tendsto (fun t : ℝ => -(c * (t - h))) atTop atBot :=
      tendsto_neg_atTop_atBot.comp h2
    have h4 := Real.tendsto_exp_atBot.comp h3
    have h5 := h4.const_mul (-(1 / c))
    simpa using h5
  have hres := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint hlim
  rw [hres]
  simp

/-! ### 3. Head and tail -/

theorem kix_head_ge {x A h : ℝ} (hA : 0 < A) (hh : 0 < h) (hxh : |x| * h ≤ 1) :
    Real.exp (-(A * Real.cosh h)) * (1 / 2) * h
      ≤ ∫ w in Ioc (0 : ℝ) h, kixTerm 0 x A w := by
  have hint : IntegrableOn (kixTerm 0 x A) (Ioc (0 : ℝ) h) :=
    (kixTerm_integrableOn 0 x hA).mono_set Ioc_subset_Ioi_self
  have hpt : ∀ w ∈ Ioc (0 : ℝ) h,
      Real.exp (-(A * Real.cosh h)) * (1 / 2) ≤ kixTerm 0 x A w := by
    intro w hw
    obtain ⟨hw0, hwh⟩ := hw
    have hcos : (1 : ℝ) / 2 ≤ Real.cos (x * w) := by
      have hb : (x * w) ^ 2 ≤ 1 := by
        have h1 : |x * w| ≤ 1 := by
          rw [abs_mul, abs_of_nonneg (le_of_lt hw0)]
          calc |x| * w ≤ |x| * h :=
                mul_le_mul_of_nonneg_left hwh (abs_nonneg x)
            _ ≤ 1 := hxh
        nlinarith [abs_nonneg (x * w), sq_abs (x * w), h1]
      have := Real.one_sub_sq_div_two_le_cos (x := x * w)
      linarith
    have hexp : Real.exp (-(A * Real.cosh h)) ≤ Real.exp (-(A * Real.cosh w)) := by
      refine Real.exp_le_exp.mpr ?_
      have hcw : Real.cosh w ≤ Real.cosh h := cosh_le_cosh_of_le (le_of_lt hw0) hwh
      nlinarith
    rw [kixTerm_zero_eq]
    have hE : (0 : ℝ) < Real.exp (-(A * Real.cosh h)) := Real.exp_pos _
    calc Real.exp (-(A * Real.cosh h)) * (1 / 2)
        ≤ Real.exp (-(A * Real.cosh h)) * Real.cos (x * w) :=
          mul_le_mul_of_nonneg_left hcos hE.le
      _ ≤ Real.exp (-(A * Real.cosh w)) * Real.cos (x * w) := by
          refine mul_le_mul_of_nonneg_right hexp ?_
          linarith
  have hconst : (∫ _w in Ioc (0 : ℝ) h, Real.exp (-(A * Real.cosh h)) * (1 / 2))
      = Real.exp (-(A * Real.cosh h)) * (1 / 2) * h := by
    rw [setIntegral_const, Real.volume_real_Ioc_of_le (le_of_lt hh), sub_zero, smul_eq_mul]
    ring
  calc Real.exp (-(A * Real.cosh h)) * (1 / 2) * h
      = ∫ _w in Ioc (0 : ℝ) h, Real.exp (-(A * Real.cosh h)) * (1 / 2) := hconst.symm
    _ ≤ ∫ w in Ioc (0 : ℝ) h, kixTerm 0 x A w := by
        refine setIntegral_mono_on (integrableOn_const ?_) hint measurableSet_Ioc hpt
        rw [Real.volume_Ioc]
        exact ENNReal.ofReal_ne_top

theorem kix_tail_abs_le {x A h : ℝ} (hA : 0 < A) (hh : 0 < h) :
    |∫ w in Ioi h, kixTerm 0 x A w|
      ≤ Real.exp (-(A * Real.cosh h)) * (1 / (A * Real.sinh h)) := by
  have hsh : 0 < Real.sinh h := Real.sinh_pos_iff.mpr hh
  have hc : 0 < A * Real.sinh h := mul_pos hA hsh
  have hbnd : IntegrableOn
      (fun w => Real.exp (-(A * Real.cosh h)) *
        Real.exp (-((A * Real.sinh h) * (w - h)))) (Ioi h) := by
    have hfun : (fun w : ℝ => Real.exp (-((A * Real.sinh h) * (w - h))))
        = fun w : ℝ => Real.exp ((A * Real.sinh h) * h) *
            Real.exp (-(A * Real.sinh h) * w) := by
      funext w
      rw [← Real.exp_add]
      congr 1
      ring
    have h1 : IntegrableOn (fun w : ℝ =>
        Real.exp (-((A * Real.sinh h) * (w - h)))) (Ioi h) := by
      rw [hfun]
      exact (exp_neg_integrableOn_Ioi h hc).const_mul _
    exact h1.const_mul _
  have hpt : ∀ w ∈ Ioi h, ‖kixTerm 0 x A w‖
      ≤ Real.exp (-(A * Real.cosh h)) * Real.exp (-((A * Real.sinh h) * (w - h))) := by
    intro w hw
    have hwh : h ≤ w := le_of_lt hw
    have htan := cosh_tangent_lower (le_of_lt hh) hwh
    have hb1 : |kixTerm 0 x A w| ≤ Real.cosh w ^ 0 * Real.exp (-(A * Real.cosh w)) :=
      kixTerm_abs_le_cosh 0 x A w
    rw [pow_zero, one_mul] at hb1
    have hb2 : Real.exp (-(A * Real.cosh w))
        ≤ Real.exp (-(A * Real.cosh h)) * Real.exp (-((A * Real.sinh h) * (w - h))) := by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      nlinarith [htan, hA]
    rw [Real.norm_eq_abs]
    linarith
  calc |∫ w in Ioi h, kixTerm 0 x A w|
      = ‖∫ w in Ioi h, kixTerm 0 x A w‖ := by rw [Real.norm_eq_abs]
    _ ≤ ∫ w in Ioi h, Real.exp (-(A * Real.cosh h)) *
          Real.exp (-((A * Real.sinh h) * (w - h))) := by
        refine norm_integral_le_of_norm_le hbnd ?_
        filter_upwards [ae_restrict_mem (measurableSet_Ioi (a := h))] with w hw
        exact hpt w hw
    _ = Real.exp (-(A * Real.cosh h)) * (1 / (A * Real.sinh h)) := by
        rw [integral_const_mul, integral_exp_neg_shift hc]

/-! ### 4. Positivity of `K_{ix}` above the explicit threshold -/

/-- **`K_{ix}(A) > 0` for `A > 4(|x|+1)²`.**  Unconditional, explicit, and proved from the
integral representation by the head/tail split above. -/
theorem kix_zero_pos {x A : ℝ} (hA : 4 * (|x| + 1) ^ 2 < A) : 0 < kix 0 x A := by
  set h : ℝ := 1 / (|x| + 1) with hhdef
  have hx1 : (0 : ℝ) < |x| + 1 := by positivity
  have hh : 0 < h := by rw [hhdef]; positivity
  have hA0 : 0 < A := lt_of_le_of_lt (by positivity) hA
  have hxh : |x| * h ≤ 1 := by
    rw [hhdef, mul_one_div, div_le_one hx1]
    linarith
  have hsh : 0 < Real.sinh h := Real.sinh_pos_iff.mpr hh
  have hM : (0 : ℝ) < Real.exp (-(A * Real.cosh h)) := Real.exp_pos _
  -- split the ray
  have hdisj : Disjoint (Ioc (0 : ℝ) h) (Ioi h) := by
    rw [Set.disjoint_left]
    intro a ha hb
    exact absurd hb (by simpa using ha.2)
  have hi1 : IntegrableOn (kixTerm 0 x A) (Ioc (0 : ℝ) h) :=
    (kixTerm_integrableOn 0 x hA0).mono_set Ioc_subset_Ioi_self
  have hi2 : IntegrableOn (kixTerm 0 x A) (Ioi h) :=
    (kixTerm_integrableOn 0 x hA0).mono_set (Ioi_subset_Ioi (le_of_lt hh))
  have hsplit : kix 0 x A
      = (∫ w in Ioc (0 : ℝ) h, kixTerm 0 x A w) + ∫ w in Ioi h, kixTerm 0 x A w := by
    unfold kix
    rw [← Set.Ioc_union_Ioi_eq_Ioi (le_of_lt hh),
      setIntegral_union hdisj measurableSet_Ioi hi1 hi2]
  have hhead := kix_head_ge hA0 hh hxh
  have htail := kix_tail_abs_le (x := x) hA0 hh
  have htail' : -(Real.exp (-(A * Real.cosh h)) * (1 / (A * Real.sinh h)))
      ≤ ∫ w in Ioi h, kixTerm 0 x A w := neg_le_of_abs_le htail
  -- the threshold comparison
  have hAh : 4 < A * h ^ 2 := by
    have hx2 : (0 : ℝ) < (|x| + 1) ^ 2 := by positivity
    have hhsq : h ^ 2 = 1 / (|x| + 1) ^ 2 := by rw [hhdef, div_pow, one_pow]
    rw [hhsq, mul_one_div, lt_div_iff₀ hx2]
    linarith [hA]
  have hshh : h / 2 ≤ Real.sinh h := half_le_sinh (le_of_lt hh)
  have hkey : 2 < A * h * Real.sinh h := by
    have h1 : A * h * (h / 2) ≤ A * h * Real.sinh h := by
      refine mul_le_mul_of_nonneg_left hshh ?_
      positivity
    nlinarith [hAh, h1, hh, hA0]
  have hcmp : Real.exp (-(A * Real.cosh h)) * (1 / (A * Real.sinh h))
      < Real.exp (-(A * Real.cosh h)) * (1 / 2) * h := by
    have hc : 0 < A * Real.sinh h := mul_pos hA0 hsh
    have hstep : 1 / (A * Real.sinh h) < (1 / 2) * h := by
      rw [div_lt_iff₀ hc]
      nlinarith [hkey]
    calc Real.exp (-(A * Real.cosh h)) * (1 / (A * Real.sinh h))
        < Real.exp (-(A * Real.cosh h)) * ((1 / 2) * h) :=
          mul_lt_mul_of_pos_left hstep hM
      _ = Real.exp (-(A * Real.cosh h)) * (1 / 2) * h := by ring
  rw [hsplit]
  linarith

/-! ### 5. Obligation A, hypothesis-free -/

/-- **OBLIGATION A, HYPOTHESIS-FREE.**  For every `a` above both `8` and the explicit
turning threshold `4(|x|+1)²`,

  `0 < (A² + 9)·K_{ix}(A) + 6A·K′_{ix}(A)`   for all `A ≥ a`,

with `K_{ix}` the compiled integral representation and `K′_{ix}` its genuine derivative.
No positivity, no derivative bound, and no ODE fact appears as a hypothesis. -/
theorem radial_kix_pos_uncond {x a : ℝ} (ha8 : 8 ≤ a) (hax : 4 * (|x| + 1) ^ 2 < a) :
    ∀ A ∈ Ici a, 0 < (A ^ 2 + 9) * kix 0 x A + 6 * A * kix 1 x A := by
  refine radial_kix_pos ha8 ?_
  intro A hA
  exact kix_zero_pos (lt_of_lt_of_le hax hA)

/-- The same statement with an explicit single threshold. -/
theorem radial_kix_pos_at {x A : ℝ} (h8 : 8 ≤ A) (hx : 4 * (|x| + 1) ^ 2 < A) :
    0 < (A ^ 2 + 9) * kix 0 x A + 6 * A * kix 1 x A :=
  radial_kix_pos_uncond h8 hx A (mem_Ici.mpr le_rfl)

end C3B6.Bessel

section AxiomAudit
#print axioms C3B6.Bessel.cosh_le_cosh_of_le
#print axioms C3B6.Bessel.half_le_sinh
#print axioms C3B6.Bessel.cosh_tangent_lower
#print axioms C3B6.Bessel.integral_exp_neg_shift
#print axioms C3B6.Bessel.kix_head_ge
#print axioms C3B6.Bessel.kix_tail_abs_le
#print axioms C3B6.Bessel.kix_zero_pos
#print axioms C3B6.Bessel.radial_kix_pos_uncond
#print axioms C3B6.Bessel.radial_kix_pos_at
end AxiomAudit
