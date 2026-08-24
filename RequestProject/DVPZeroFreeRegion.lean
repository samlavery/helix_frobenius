import RequestProject.DVPGrowthBounds
import RequestProject.SeatScalarCriterion

/-!
# DVP campaign, brick B4: the zero-free region

Sub-bricks: (B4a) the pole bound `‖ζ(1+x)‖ ≤ A/x` on `(0,1]`; (B4b) the
classical 3-4-1 inequality in ζ-values, from mathlib's public
`norm_LSeries_product_ge_one`; then the assembly.
-/

open Complex Filter Topology

noncomputable section

namespace CriticalLinePhasor.DVP

/-- **B4a: the pole bound** — `∃ A > 0` with `‖ζ(1+x)‖ ≤ A/x` for
`0 < x ≤ 1`. -/
theorem zeta_pole_bound : ∃ A : ℝ, 0 < A ∧ ∀ x : ℝ, 0 < x → x ≤ 1 →
    ‖riemannZeta ((1 : ℂ) + (x : ℂ))‖ ≤ A / x := by
  -- eventually ‖(s−1)ζ(s)‖ ≤ 2 near 1
  have hev : ∀ᶠ s in 𝓝[≠] (1:ℂ), ‖(s - 1) * riemannZeta s‖ ≤ 2 := by
    have h2 : ∀ᶠ w in 𝓝 (1:ℂ), ‖w‖ ≤ 2 := by
      have hball : Metric.closedBall (1:ℂ) 1 ∈ 𝓝 (1:ℂ) :=
        Metric.closedBall_mem_nhds _ (by norm_num)
      filter_upwards [hball] with w hw
      rw [Metric.mem_closedBall, dist_eq_norm] at hw
      calc ‖w‖ = ‖(w - 1) + 1‖ := by ring_nf
        _ ≤ ‖w - 1‖ + ‖(1:ℂ)‖ := norm_add_le _ _
        _ ≤ 2 := by
            simp only [norm_one]
            linarith
    exact riemannZeta_residue_one.eventually h2
  -- restrict along x ↦ 1 + x from the right
  have hmap : Tendsto (fun x : ℝ => (1:ℂ) + (x:ℂ)) (𝓝[>] (0:ℝ))
      (𝓝[≠] (1:ℂ)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have h1 : Tendsto (fun x : ℝ => (1:ℂ) + (x:ℂ)) (𝓝 0) (𝓝 ((1:ℂ) + 0)) :=
        (Complex.continuous_ofReal.tendsto 0).const_add _
      simpa using h1.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      rw [Set.mem_Ioi] at hx
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro h
      have hx0 : (x:ℂ) = 0 := by linear_combination h
      have : x = 0 := by exact_mod_cast hx0
      linarith
  have hev2 : ∀ᶠ x : ℝ in 𝓝[>] (0:ℝ), ‖riemannZeta ((1:ℂ) + (x:ℂ))‖ ≤ 2 / x := by
    filter_upwards [hmap.eventually hev, self_mem_nhdsWithin] with x hx hxpos
    rw [Set.mem_Ioi] at hxpos
    rw [show ((1:ℂ) + (x:ℂ) - 1) = (x:ℂ) by ring, norm_mul] at hx
    have hxn : ‖(x:ℂ)‖ = x := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hxpos]
    rw [hxn] at hx
    rw [le_div_iff₀ hxpos]
    linarith [hx]
  -- extract δ
  rw [Filter.Eventually, Metric.mem_nhdsWithin_iff] at hev2
  obtain ⟨δ, hδpos, hδsub⟩ := hev2
  have hδ : ∀ x : ℝ, 0 < x → x < δ → ‖riemannZeta ((1:ℂ) + (x:ℂ))‖ ≤ 2 / x := by
    intro x hx0 hxδ
    apply hδsub
    constructor
    · rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hx0]
      exact hxδ
    · exact hx0
  set δ' : ℝ := min δ 1 with hδ'def
  have hδ'pos : 0 < δ' := lt_min hδpos (by norm_num)
  have hδ'le : δ' ≤ 1 := min_le_right _ _
  -- compact part
  have hcont : ContinuousOn (fun x : ℝ => riemannZeta ((1:ℂ) + (x:ℂ)))
      (Set.Icc δ' 1) := by
    intro x hx
    have hne : (1:ℂ) + (x:ℂ) ≠ 1 := by
      intro h
      have hx0 : (x:ℂ) = 0 := by linear_combination h
      have : x = 0 := by exact_mod_cast hx0
      have := hx.1
      linarith [hδ'pos]
    have h1 : ContinuousAt (fun x : ℝ => (1:ℂ) + (x:ℂ)) x :=
      (Complex.continuous_ofReal.const_add 1).continuousAt
    have h2 : ContinuousAt riemannZeta ((1:ℂ) + (x:ℂ)) :=
      (differentiableAt_riemannZeta hne).continuousAt
    exact (ContinuousAt.comp (f := fun x : ℝ => (1:ℂ) + (x:ℂ))
      h2 h1).continuousWithinAt
  obtain ⟨M, hM⟩ := (isCompact_Icc).exists_bound_of_continuousOn hcont
  refine ⟨max 2 (max M 1), by positivity, fun x hx0 hx1 => ?_⟩
  rcases lt_or_ge x δ' with hlt | hge
  · have hdist : x < δ := lt_of_lt_of_le hlt (min_le_left _ _)
    calc ‖riemannZeta ((1:ℂ) + (x:ℂ))‖ ≤ 2 / x := hδ x hx0 hdist
      _ ≤ max 2 (max M 1) / x := by
          have hnum : (2:ℝ) ≤ max 2 (max M 1) := le_max_left _ _
          gcongr
  · have hM' := hM x ⟨hge, hx1⟩
    have hmax1 : (1:ℝ) ≤ max M 1 := le_max_right _ _
    have hmaxM : M ≤ max M 1 := le_max_left _ _
    calc ‖riemannZeta ((1:ℂ) + (x:ℂ))‖ ≤ M := hM'
      _ ≤ max M 1 := hmaxM
      _ ≤ max M 1 / x := by
          rw [le_div_iff₀ hx0]
          nlinarith
      _ ≤ max 2 (max M 1) / x := by
          have hnum : max M 1 ≤ max 2 (max M 1) := le_max_right _ _
          gcongr

/-- **B4b: the 3-4-1 inequality in ζ-values** — for `x > 0` and every `y`:
`1 ≤ ‖ζ(1+x)‖³·‖ζ(1+x+iy)‖⁴·‖ζ(1+x+2iy)‖`. -/
theorem zeta_341 {x : ℝ} (hx : 0 < x) (y : ℝ) :
    1 ≤ ‖riemannZeta ((1:ℂ) + x)‖ ^ 3 * ‖riemannZeta ((1:ℂ) + x + I * y)‖ ^ 4 *
      ‖riemannZeta ((1:ℂ) + x + 2 * I * y)‖ := by
  have h := DirichletCharacter.norm_LSeries_product_ge_one
    (N := 1) (χ := 1) hx y
  have h₀ : (1:ℝ) < ((1:ℂ) + x).re := by
    simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re]
    linarith
  have h₁ : (1:ℝ) < ((1:ℂ) + x + I * y).re := by
    simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re,
      Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im]
    ring_nf
    linarith
  have h₂ : (1:ℝ) < ((1:ℂ) + x + 2 * I * y).re := by
    simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re,
      Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im,
      Complex.re_ofNat, Complex.im_ofNat]
    ring_nf
    linarith
  rw [DirichletCharacter.LSeries_modOne_eq, one_pow,
    DirichletCharacter.LSeries_modOne_eq] at h
  rw [LSeries_one_eq_riemannZeta h₀, LSeries_one_eq_riemannZeta h₁,
    LSeries_one_eq_riemannZeta h₂] at h
  calc (1:ℝ) ≤ ‖riemannZeta ((1:ℂ) + x) ^ 3 * riemannZeta ((1:ℂ) + x + I * y) ^ 4 *
        riemannZeta ((1:ℂ) + x + 2 * I * y)‖ := h
    _ = ‖riemannZeta ((1:ℂ) + x)‖ ^ 3 * ‖riemannZeta ((1:ℂ) + x + I * y)‖ ^ 4 *
        ‖riemannZeta ((1:ℂ) + x + 2 * I * y)‖ := by
        rw [norm_mul, norm_mul, norm_pow, norm_pow]

/-- **B4c: the segment bound** — from a zero `β+iγ` with `β` inside the B3
region, the value at `1+x+iγ` is controlled by the distance to the zero times
the derivative bound: `‖ζ(1+x+iγ)‖ ≤ (1+x−β)·120e·log²|γ|`. -/
theorem zeta_segment_bound {β γ x : ℝ}
    (hζ0 : riemannZeta ((β : ℂ) + I * γ) = 0)
    (hγ : Real.exp 2 + 1 ≤ |γ|)
    (hβl : 1 - 1/(4 * Real.log |γ|) ≤ β) (hβu : β ≤ 1)
    (hx : 0 < x) (hx4 : x ≤ 1/4) :
    ‖riemannZeta ((1 + x : ℝ) + I * γ)‖
      ≤ (1 + x - β) * (120 * Real.exp 1 * (Real.log |γ|)^2) := by
  have hγpos : (0:ℝ) < |γ| := by linarith [Real.exp_pos 2]
  have hγne : γ ≠ 0 := by
    intro h
    rw [h] at hγ
    simp at hγ
    linarith [Real.exp_pos 2, hγ]
  have hL2 : (2:ℝ) ≤ Real.log |γ| := by
    have h1 : Real.exp 2 ≤ |γ| := by linarith
    have := Real.log_le_log (Real.exp_pos 2) h1
    rwa [Real.log_exp] at this
  have hβx : β ≤ 1 + x := by linarith
  -- every segment point is off 1 and in the B3 region
  have hseg : ∀ u : ℝ, u ∈ Set.uIcc β (1 + x) →
      ((u : ℂ) + I * γ ≠ 1) ∧
      Real.exp 2 + 1 ≤ |((u : ℂ) + I * γ).im| ∧
      1 - 1/(4 * Real.log |((u : ℂ) + I * γ).im|) ≤ ((u : ℂ) + I * γ).re ∧
      ((u : ℂ) + I * γ).re ≤ 3/2 := by
    intro u hu
    rw [Set.uIcc_of_le hβx] at hu
    have him : ((u : ℂ) + I * γ).im = γ := by simp
    have hre : ((u : ℂ) + I * γ).re = u := by simp
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h
      have := congrArg Complex.im h
      rw [him] at this
      simp at this
      exact hγne this
    · rw [him]
      exact hγ
    · rw [him, hre]
      linarith [hu.1]
    · rw [hre]
      linarith [hu.2]
  -- the real-parameter derivative
  have hg : ∀ u : ℝ, u ∈ Set.uIcc β (1 + x) →
      HasDerivAt (fun v : ℝ => riemannZeta ((v : ℂ) + I * γ))
        (deriv riemannZeta ((u : ℂ) + I * γ)) u := by
    intro u hu
    have hne := (hseg u hu).1
    have h1 : HasDerivAt (fun z : ℂ => riemannZeta (z + I * γ))
        (deriv riemannZeta ((u : ℂ) + I * γ)) (u : ℂ) := by
      have hζd : HasDerivAt riemannZeta
          (deriv riemannZeta ((u : ℂ) + I * γ)) ((u : ℂ) + I * γ) :=
        (differentiableAt_riemannZeta hne).hasDerivAt
      have hlin : HasDerivAt (fun z : ℂ => z + I * γ) 1 (u : ℂ) := by
        simpa using (hasDerivAt_id ((u:ℂ))).add_const (I * γ)
      have h2 := hζd.comp (u : ℂ) hlin
      rw [mul_one] at h2
      exact h2
    exact h1.comp_ofReal
  -- continuity of the derivative along the segment
  have hcont : ContinuousOn (fun u : ℝ => deriv riemannZeta ((u : ℂ) + I * γ))
      (Set.uIcc β (1 + x)) := by
    intro u hu
    have hne := (hseg u hu).1
    have han : AnalyticAt ℂ riemannZeta ((u : ℂ) + I * γ) := by
      have hopen : IsOpen {s : ℂ | s ≠ 1} := isOpen_compl_singleton
      have hdiff : DifferentiableOn ℂ riemannZeta {s : ℂ | s ≠ 1} :=
        fun z hz => (differentiableAt_riemannZeta hz).differentiableWithinAt
      exact (hdiff.analyticOnNhd hopen) _ hne
    have hderiv_cont : ContinuousAt (deriv riemannZeta) ((u : ℂ) + I * γ) :=
      han.deriv.continuousAt
    have h1 : ContinuousAt (fun u : ℝ => (u : ℂ) + I * γ) u :=
      (Complex.continuous_ofReal.add_const _).continuousAt
    exact (ContinuousAt.comp (f := fun u : ℝ => (u : ℂ) + I * γ)
      hderiv_cont h1).continuousWithinAt
  -- FTC
  have hint : IntervalIntegrable
      (fun u : ℝ => deriv riemannZeta ((u : ℂ) + I * γ))
      MeasureTheory.volume β (1 + x) := hcont.intervalIntegrable
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u hu => hg u hu) hint
  have hval : (∫ u : ℝ in β..(1 + x), deriv riemannZeta ((u : ℂ) + I * γ))
      = riemannZeta (((1 + x : ℝ) : ℂ) + I * γ) := by
    rw [hftc]
    have hzero : riemannZeta (((β : ℝ) : ℂ) + I * γ) = 0 := hζ0
    rw [hzero]
    push_cast
    ring
  rw [show ((1 + x : ℝ) : ℂ) + I * γ = (((1 + x : ℝ) : ℂ) + I * γ) from rfl,
    ← hval]
  calc ‖∫ u : ℝ in β..(1 + x), deriv riemannZeta ((u : ℂ) + I * γ)‖
      ≤ (120 * Real.exp 1 * (Real.log |γ|)^2) * |(1 + x) - β| := by
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro u hu
        have hmem : u ∈ Set.uIcc β (1 + x) := Set.uIoc_subset_uIcc hu
        obtain ⟨_, hγ', hβl', hβu'⟩ := hseg u hmem
        have hB3 := zeta_deriv_log_sq_growth hγ' hβl' hβu'
        have him : ((u : ℂ) + I * γ).im = γ := by simp
        rw [him] at hB3
        exact hB3
    _ = (1 + x - β) * (120 * Real.exp 1 * (Real.log |γ|)^2) := by
        rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ (1 + x) - β)]
        ring

set_option maxHeartbeats 3200000 in
/-- **B4d: THE ZERO-FREE REGION** — there is `c > 0` such that every zero
`β + iγ` of ζ with `|γ| ≥ e² + 1` satisfies `β ≤ 1 − c/log⁹|γ|`.

The `|ζ|`-product route (3-4-1 + pole + growth + segment) gives exponent 9;
the classical exponent 1 needs the log-derivative version and is deferred. -/
theorem zero_free_region : ∃ c : ℝ, 0 < c ∧ ∀ β γ : ℝ,
    riemannZeta ((β : ℂ) + I * γ) = 0 → 0 < β → β ≤ 1 →
    Real.exp 2 + 1 ≤ |γ| →
    β ≤ 1 - c / (Real.log |γ|) ^ 9 := by
  obtain ⟨A, hApos, hA⟩ := zeta_pole_bound
  set K : ℝ := 120 * Real.exp 1 with hKdef
  have hKpos : (0:ℝ) < K := by rw [hKdef]; positivity
  set E4 : ℝ := 1 / (30 * Real.exp 1 * A^3 * K^4) with hE4def
  have hE4pos : (0:ℝ) < E4 := by rw [hE4def]; positivity
  set E : ℝ := E4 ^ ((1:ℝ)/4) with hEdef
  have hEpos : (0:ℝ) < E := Real.rpow_pos_of_pos hE4pos _
  set t : ℝ := min ((3 * E / 4) ^ (4:ℕ)) (1/4) with htdef
  have htpos : (0:ℝ) < t := lt_min (by positivity) (by norm_num)
  have ht4 : t ≤ 1/4 := min_le_right _ _
  set c : ℝ := min ((E / 4) * t ^ ((3:ℝ)/4)) (1/4) with hcdef
  have hcpos : (0:ℝ) < c := lt_min (by positivity) (by norm_num)
  refine ⟨c, hcpos, fun β γ hζ0 hβ0 hβ1 hγ => ?_⟩
  set L : ℝ := Real.log |γ| with hLdef
  have hγpos : (0:ℝ) < |γ| := by linarith [Real.exp_pos 2]
  have hL2 : (2:ℝ) ≤ L := by
    rw [hLdef]
    have h1 : Real.exp 2 ≤ |γ| := by linarith
    have := Real.log_le_log (Real.exp_pos 2) h1
    rwa [Real.log_exp] at this
  have hLpos : (0:ℝ) < L := by linarith
  have hL9pos : (0:ℝ) < L ^ 9 := by positivity
  -- easy case: β already below the B3 region
  rcases lt_or_ge β (1 - 1/(4*L)) with hcase | hcase
  · have h1 : c / L ^ 9 ≤ 1 / (4 * L) := by
      rw [div_le_div_iff₀ hL9pos (by positivity)]
      have hc4 : c ≤ 1/4 := min_le_right _ _
      have hL8 : (2:ℝ)^8 ≤ L^8 := by
        apply pow_le_pow_left₀ (by norm_num) hL2
      nlinarith [hL8, hLpos]
    linarith
  -- main case: the zero is inside the B3 strip; run the 3-4-1 chase
  · set x : ℝ := t / L ^ 9 with hxdef
    have hxpos : (0:ℝ) < x := by rw [hxdef]; positivity
    have hx4 : x ≤ 1/4 := by
      rw [hxdef]
      have h1 : (1:ℝ) ≤ L ^ 9 := by
        calc (1:ℝ) ≤ 2^9 := by norm_num
          _ ≤ L^9 := by
              apply pow_le_pow_left₀ (by norm_num) hL2
      calc t / L ^ 9 ≤ t / 1 := by
            apply div_le_div_of_nonneg_left (le_of_lt htpos) (by norm_num) h1
        _ = t := by ring
        _ ≤ 1/4 := ht4
    have hx1 : x ≤ 1 := by linarith
    -- the four inputs
    have h341 := zeta_341 hxpos γ
    have hpole := hA x hxpos hx1
    have hseg := zeta_segment_bound hζ0 hγ hcase hβ1 hxpos hx4
    have him_eq : ((1:ℂ) + x + 2 * I * γ).im = 2 * γ := by
      simp [Complex.add_im, Complex.mul_im]
    have hre_eq : ((1:ℂ) + x + 2 * I * γ).re = 1 + x := by
      simp [Complex.add_re, Complex.mul_re]
    have habs2 : |(2:ℝ) * γ| = 2 * |γ| := by
      rw [abs_mul]
      norm_num
    have hgrow : ‖riemannZeta ((1:ℂ) + x + 2 * I * γ)‖ ≤ 30 * Real.exp 1 * L := by
      have hHe : Real.exp 2 ≤ |((1:ℂ) + x + 2 * I * γ).im| := by
        rw [him_eq, habs2]
        linarith
      have hHσ : 1 - 1 / Real.log |((1:ℂ) + x + 2 * I * γ).im|
          ≤ ((1:ℂ) + x + 2 * I * γ).re := by
        rw [him_eq, hre_eq, habs2]
        have hlogpos : (0:ℝ) < Real.log (2 * |γ|) := by
          apply Real.log_pos
          linarith [Real.exp_pos 2]
        have h0 : (0:ℝ) ≤ 1 / Real.log (2 * |γ|) := by positivity
        linarith
      have hHu : ((1:ℂ) + x + 2 * I * γ).re ≤ 2 := by
        rw [hre_eq]
        linarith
      have h := zeta_log_growth hHe hHσ hHu
      have hlog2 : Real.log |((1:ℂ) + x + 2 * I * γ).im| ≤ 2 * L := by
        rw [him_eq, habs2]
        have h4 : (4:ℝ) ≤ |γ| := by
          have := Real.add_one_le_exp (2:ℝ)
          linarith
        have h1 : 2 * |γ| ≤ |γ| ^ 2 := by nlinarith
        calc Real.log (2 * |γ|) ≤ Real.log (|γ| ^ 2) :=
            Real.log_le_log (by positivity) h1
          _ = 2 * L := by
              rw [hLdef, Real.log_pow]
              push_cast
              ring
      calc ‖riemannZeta ((1:ℂ) + x + 2 * I * γ)‖
          ≤ 15 * Real.exp 1 * Real.log |((1:ℂ) + x + 2 * I * γ).im| := h
        _ ≤ 15 * Real.exp 1 * (2 * L) := by
            apply mul_le_mul_of_nonneg_left hlog2 (by positivity)
        _ = 30 * Real.exp 1 * L := by ring
    -- normalize the segment bound's cast
    have hseg' : ‖riemannZeta ((1:ℂ) + x + I * γ)‖ ≤ (1 + x - β) * (K * L ^ 2) := by
      have hcast : (((1 + x : ℝ)) : ℂ) + I * γ = (1:ℂ) + x + I * γ := by
        push_cast
        ring
      rw [hcast] at hseg
      calc ‖riemannZeta ((1:ℂ) + x + I * γ)‖
          ≤ (1 + x - β) * (120 * Real.exp 1 * (Real.log |γ|) ^ 2) := hseg
        _ = (1 + x - β) * (K * L ^ 2) := by rw [hKdef, hLdef]
    set G : ℝ := 1 + x - β with hGdef
    have hGpos : (0:ℝ) < G := by rw [hGdef]; linarith
    -- the product chase
    have hprod : (1:ℝ) ≤ (A / x) ^ 3 * (G * (K * L ^ 2)) ^ 4 *
        (30 * Real.exp 1 * L) := by
      calc (1:ℝ) ≤ ‖riemannZeta ((1:ℂ) + x)‖ ^ 3 *
            ‖riemannZeta ((1:ℂ) + x + I * γ)‖ ^ 4 *
            ‖riemannZeta ((1:ℂ) + x + 2 * I * γ)‖ := h341
        _ ≤ (A / x) ^ 3 * (G * (K * L ^ 2)) ^ 4 * (30 * Real.exp 1 * L) := by
            apply mul_le_mul
            · apply mul_le_mul
              · exact pow_le_pow_left₀ (norm_nonneg _) hpole 3
              · exact pow_le_pow_left₀ (norm_nonneg _) hseg' 4
              · positivity
              · positivity
            · exact hgrow
            · exact norm_nonneg _
            · positivity
    -- extract G⁴ ≥ E4·x³/L⁹
    have hx3 : (0:ℝ) < x ^ 3 := by positivity
    have hG4 : E4 * x ^ 3 / L ^ 9 ≤ G ^ 4 := by
      have hexpand : (A / x) ^ 3 * (G * (K * L ^ 2)) ^ 4 * (30 * Real.exp 1 * L)
          = (A ^ 3 * G ^ 4 * K ^ 4 * L ^ 9 * (30 * Real.exp 1)) / x ^ 3 := by
        field_simp
      rw [hexpand, le_div_iff₀ hx3] at hprod
      have hDpos : (0:ℝ) < 30 * Real.exp 1 * A ^ 3 * K ^ 4 := by positivity
      rw [hE4def, div_le_iff₀ hL9pos, one_div, inv_mul_eq_div,
        div_le_iff₀ hDpos]
      nlinarith [hprod]
    -- fourth root with x = t/L⁹
    have hxcube : x ^ 3 = t ^ 3 / L ^ 27 := by
      rw [hxdef]
      field_simp
    have hG4' : (E4 * t ^ 3) / L ^ 36 ≤ G ^ 4 := by
      have heq : E4 * x ^ 3 / L ^ 9 = (E4 * t ^ 3) / L ^ 36 := by
        rw [hxcube]
        field_simp
      linarith [heq ▸ hG4]
    set g : ℝ := (E4 * t ^ 3) ^ ((1:ℝ)/4) / L ^ 9 with hgdef
    have hgpos : (0:ℝ) < g := by
      rw [hgdef]
      have : (0:ℝ) < (E4 * t ^ 3) ^ ((1:ℝ)/4) :=
        Real.rpow_pos_of_pos (by positivity) _
      positivity
    have hg4 : g ^ 4 = (E4 * t ^ 3) / L ^ 36 := by
      rw [hgdef, div_pow]
      congr 1
      · rw [← Real.rpow_natCast ((E4 * t ^ 3) ^ ((1:ℝ)/4)) 4,
          ← Real.rpow_mul (by positivity)]
        norm_num
      · rw [← pow_mul]
    have hGg : g ≤ G := by
      have h4 : g ^ 4 ≤ G ^ 4 := by
        rw [hg4]
        exact hG4'
      exact le_of_pow_le_pow_left₀ (by norm_num) (le_of_lt hGpos) h4
    -- the gain: g ≥ (E/4)·t^{3/4}/L⁹ ≥ c/L⁹ + x
    have hEt : (E4 * t ^ 3) ^ ((1:ℝ)/4) = E * t ^ ((3:ℝ)/4) := by
      rw [Real.mul_rpow (le_of_lt hE4pos) (by positivity), hEdef]
      congr 1
      rw [← Real.rpow_natCast t 3, ← Real.rpow_mul (le_of_lt htpos)]
      norm_num
    have ht14 : t ^ ((1:ℝ)/4) ≤ 3 * E / 4 := by
      have h1 : t ≤ (3 * E / 4) ^ (4:ℕ) := min_le_left _ _
      calc t ^ ((1:ℝ)/4) ≤ ((3 * E / 4) ^ (4:ℕ)) ^ ((1:ℝ)/4) :=
          Real.rpow_le_rpow (le_of_lt htpos) h1 (by norm_num)
        _ = 3 * E / 4 := by
            rw [← Real.rpow_natCast (3 * E / 4) 4,
              ← Real.rpow_mul (by positivity)]
            norm_num
    have htsplit : t = t ^ ((1:ℝ)/4) * t ^ ((3:ℝ)/4) := by
      rw [← Real.rpow_add htpos]
      norm_num
    have hgain : x + (E / 4) * t ^ ((3:ℝ)/4) / L ^ 9 ≤ g := by
      have ht34pos : (0:ℝ) < t ^ ((3:ℝ)/4) := Real.rpow_pos_of_pos htpos _
      have hkey : t + (E / 4) * t ^ ((3:ℝ)/4) ≤ E * t ^ ((3:ℝ)/4) := by
        have h1 : t ≤ (3 * E / 4) * t ^ ((3:ℝ)/4) := by
          calc t = t ^ ((1:ℝ)/4) * t ^ ((3:ℝ)/4) := htsplit
            _ ≤ (3 * E / 4) * t ^ ((3:ℝ)/4) :=
                mul_le_mul_of_nonneg_right ht14 (le_of_lt ht34pos)
        nlinarith
      have hsum : x + (E / 4) * t ^ ((3:ℝ)/4) / L ^ 9
          = (t + (E / 4) * t ^ ((3:ℝ)/4)) / L ^ 9 := by
        rw [hxdef]
        ring
      rw [hsum, hgdef, hEt]
      gcongr
    -- conclude
    have hcle : c ≤ (E / 4) * t ^ ((3:ℝ)/4) := min_le_left _ _
    have hfinal : β ≤ 1 - (E / 4) * t ^ ((3:ℝ)/4) / L ^ 9 := by
      have h1 : x + (E / 4) * t ^ ((3:ℝ)/4) / L ^ 9 ≤ G := le_trans hgain hGg
      rw [hGdef] at h1
      linarith
    have h2 : c / L ^ 9 ≤ (E / 4) * t ^ ((3:ℝ)/4) / L ^ 9 := by
      gcongr
    linarith

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.zeta_pole_bound
#print axioms CriticalLinePhasor.DVP.zeta_341
#print axioms CriticalLinePhasor.DVP.zeta_segment_bound
#print axioms CriticalLinePhasor.DVP.zero_free_region
end AxiomAudit

noncomputable section

namespace CriticalLinePhasor.DVP

open CriticalLinePhasor.SeatScalar Complex

set_option maxHeartbeats 1600000 in
/-- **B5: THE INTERIOR POSITIVITY RUNG.**  There is `c > 0` such that the
seat energy is nonnegative at every admissible anchor of height
`|Re w| ≥ e² + 2` and depth `|Im w| ≥ ½ − c/log⁹(|Re w| + ½)` — strictly
inside the strip.  Mechanism: the compiled zero-free region caps the depth of
every zero in the anchor's unit window strictly below the anchor's depth (the
FE partner giving the two-sided bound), so the deep-window of the
local-resonance law is empty and every term of the seat energy is
nonnegative. -/
theorem seat_interior_rung : ∃ c : ℝ, 0 < c ∧ ∀ w : ℂ,
    Real.exp 2 + 2 ≤ |w.re| →
    1/2 - c / (Real.log (|w.re| + 1/2))^9 ≤ |w.im| →
    ((1/2 + Complex.I * w) ∉ ZD.NontrivialZeros) →
    ((1/2 + Complex.I * (starRingEnd ℂ) w) ∉ ZD.NontrivialZeros) →
    (w - (starRingEnd ℂ) w ≠ 0) →
    0 ≤ (∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
        (ZD.xiOrderNat ρ.val : ℂ) *
          ((CriticalLinePhasor.HilbertPolya.spectralCoord ρ.val - w)⁻¹ *
            (CriticalLinePhasor.HilbertPolya.spectralCoord ρ.val
              - (starRingEnd ℂ) w)⁻¹)).re := by
  obtain ⟨c, hcpos, hregion⟩ := zero_free_region
  refine ⟨c, hcpos, fun w hre him hw hw' hwim => ?_⟩
  have hwindow := seat_energy_ge_window hw hw' hwim
  -- the deep-window is empty
  have hempty : IsEmpty {ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} //
      |ρ.val.im - w.re| < 1 / 2 ∧ |w.im| < |ρ.val.re - 1 / 2|} := by
    constructor
    rintro ⟨⟨ρ, hρ⟩, hnear, hdeep⟩
    simp only at hnear hdeep
    set β : ℝ := ρ.re with hβdef
    set γ : ℝ := ρ.im with hγdef
    have hβ0 : 0 < β := hρ.1
    have hβ1' : β < 1 := hρ.2.1
    have hζρ : riemannZeta ((β : ℂ) + I * γ) = 0 := by
      have hpt : (β : ℂ) + I * γ = ρ := by
        rw [hβdef, hγdef]
        apply Complex.ext <;> simp
      rw [hpt]
      exact hρ.2.2
    -- the ordinate is high
    have hγlb : |w.re| - 1/2 ≤ |γ| := by
      have h1 := abs_sub_abs_le_abs_sub w.re γ
      rw [abs_sub_comm γ w.re] at hnear
      linarith [hnear, h1]
    have hγe : Real.exp 2 + 1 ≤ |γ| := by linarith
    have hγub : |γ| ≤ |w.re| + 1/2 := by
      have h1 := abs_sub_abs_le_abs_sub γ w.re
      linarith [hnear, h1]
    set L : ℝ := Real.log |γ| with hLdef
    have hγpos : (0:ℝ) < |γ| := by linarith [Real.exp_pos 2]
    have hL2 : (2:ℝ) ≤ L := by
      rw [hLdef]
      have h1 : Real.exp 2 ≤ |γ| := by linarith
      have := Real.log_le_log (Real.exp_pos 2) h1
      rwa [Real.log_exp] at this
    have hL9pos : (0:ℝ) < L ^ 9 := by positivity
    -- region: upper bound on β
    have hβup : β ≤ 1 - c / L ^ 9 :=
      hregion β γ hζρ hβ0 (le_of_lt hβ1') hγe
    -- region at the FE partner: lower bound on β
    have hβlow : c / L ^ 9 ≤ β := by
      have hmem' :=
        CriticalLinePhasor.FoliatedGlobalPolarization.feReflect_mem hρ
      have hpt' : ((1 - β : ℝ) : ℂ) + I * γ
          = CriticalLinePhasor.FoliatedPolarization.feReflect ρ := by
        rw [CriticalLinePhasor.FoliatedPolarization.feReflect, hβdef, hγdef]
        apply Complex.ext <;> simp
      have hζ' : riemannZeta (((1 - β : ℝ) : ℂ) + I * γ) = 0 := by
        rw [hpt']
        exact hmem'.2.2
      have h := hregion (1 - β) γ hζ' (by linarith) (by linarith) hγe
      linarith
    -- depth cap
    have hdepth_cap : |β - 1/2| ≤ 1/2 - c / L ^ 9 := by
      rw [abs_le]
      constructor <;> linarith
    -- the anchor is at least that deep
    have hΛ : L ≤ Real.log (|w.re| + 1/2) := by
      rw [hLdef]
      apply Real.log_le_log hγpos
      exact hγub
    have hΛpos : (0:ℝ) < Real.log (|w.re| + 1/2) := by linarith
    have hmono : c / (Real.log (|w.re| + 1/2)) ^ 9 ≤ c / L ^ 9 := by
      apply div_le_div_of_nonneg_left (le_of_lt hcpos) hL9pos
      apply pow_le_pow_left₀ (by linarith) hΛ
    have hanchor : |β - 1/2| ≤ |w.im| := by
      calc |β - 1/2| ≤ 1/2 - c / L ^ 9 := hdepth_cap
        _ ≤ 1/2 - c / (Real.log (|w.re| + 1/2)) ^ 9 := by linarith
        _ ≤ |w.im| := him
    rw [hβdef] at hanchor
    linarith [hdeep, hanchor]
  -- empty window ⟹ zero window sum ⟹ nonneg energy
  have hzero : (∑' x : {ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} //
      |ρ.val.im - w.re| < 1 / 2 ∧ |w.im| < |ρ.val.re - 1 / 2|},
      (ZD.xiOrderNat x.val.val : ℂ) *
        ((CriticalLinePhasor.HilbertPolya.spectralCoord x.val.val - w)⁻¹ *
          (CriticalLinePhasor.HilbertPolya.spectralCoord x.val.val
            - (starRingEnd ℂ) w)⁻¹)) = 0 := by
    exact tsum_empty
  rw [hzero] at hwindow
  simpa using hwindow

end CriticalLinePhasor.DVP

section AxiomAudit2
#print axioms CriticalLinePhasor.DVP.seat_interior_rung
end AxiomAudit2
