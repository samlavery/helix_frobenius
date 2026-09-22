import RequestProject.WeilPhasorBank

/-!
# The exponential type of one off-line zero orbit under a phase-aligned Weil test (ledger 905)

In the compiled explicit formula (`weil_explicit_formula_smooth`, `weilForm_eq`) the zero side
of the Weil form for a profile `g` is `Σ'_ρ m_ρ F_g(ρ)·conj F_g(1−ρ̄)`, `F_g = laplaceTest g`.
A hypothetical zero `ρ₀ = ½ + δ + iγ₀` enters with its full FE/conjugation orbit
`ρ₀, 1−ρ₀, ρ̄₀, 1−ρ̄₀`.  This file computes that orbit exactly and bounds it for the
**phase-aligned profile** `g(x) = cos(γ₀x)·ψ(x)`, `ψ ≥ 0` a bump of radius `Λ`:

* `orbitSum_eq` — for a real even profile the four-member orbit is `4·Re(F_g(ρ₀)²)`
  (`F_g(1−s) = F_g(s)`, `F_g(s̄) = conj F_g(s)`);
* `laplaceTest_modulated` — phase alignment: `F_g(s) = ½F_ψ(s + iγ₀) + ½F_ψ(s − iγ₀)`, so at
  `ρ₀` the second term is the REAL, POSITIVE integral `A = ∫ψ(x)e^{δx}dx ≥ e^{δ(Λ−2)}`
  (`laplaceTest_ofReal_re`, `integral_mass_lower`) and the first is `F_ψ(½+δ+2iγ₀)`, bounded by
  `e^{δΛ}‖ψ''''‖₁/(2γ₀)⁴` through four integrations by parts (`laplaceTest_eq_fourth_deriv`,
  `laplaceTest_norm_le`, `iterate_deriv_eq_zero_of_radius`);
* **`orbit_lower_bound`** — `Re(orbit) ≥ ½·e^{2δ(Λ−2)}` once `γ₀⁴ ≥ ½e^{2δ}‖ψ''''‖₁` (a threshold
  independent of `Λ`), and **`orbit_upper_bound`** — `Re(orbit) ≤ 4e^{2δΛ}(∫ψ)²`.

So in the support variable `L = 2Λ` of `G = g ⋆ g̃` (primes up to `e^L` enter the prime side) the
selected orbit has exponential type exactly `δ`: `½e^{δ(L−4)} ≤ orbit ≤ 4e^{δL}(∫ψ)²`.
No `sorry`, no `axiom`.
-/

open Complex MeasureTheory Filter Topology
open scoped Real ContDiff

noncomputable section

namespace CriticalLinePhasor.ContourArgument

/-! ### The four-member orbit of a real even profile -/

/-- The Weil-form summand of a zero `ρ` for the profile `g`: `F_g(ρ)·conj F_g(1 − ρ̄)`. -/
def orbitTerm (g : ℝ → ℂ) (ρ : ℂ) : ℂ :=
  laplaceTest g ρ * (starRingEnd ℂ) (laplaceTest g (1 - (starRingEnd ℂ) ρ))

/-- The full FE/conjugation orbit of a zero: `ρ, 1−ρ, ρ̄, 1−ρ̄`. -/
def orbitSum (g : ℝ → ℂ) (ρ : ℂ) : ℂ :=
  orbitTerm g ρ + orbitTerm g (1 - ρ) + orbitTerm g ((starRingEnd ℂ) ρ)
    + orbitTerm g (1 - (starRingEnd ℂ) ρ)

/-- For an even profile, `F_g(1 − s) = F_g(s)`. -/
theorem laplaceTest_even {g : ℝ → ℂ} (hg : ∀ x, g (-x) = g x) (s : ℂ) :
    laplaceTest g (1 - s) = laplaceTest g s := by
  unfold laplaceTest
  have h := MeasureTheory.integral_neg_eq_self
    (fun x : ℝ => g x * Complex.exp ((s - 1 / 2) * x)) volume
  rw [← h]
  congr 1
  funext x
  simp only [hg]
  congr 1
  push_cast
  ring

/-- For a real profile, `F_g(s̄) = conj F_g(s)`. -/
theorem laplaceTest_conj {g : ℝ → ℂ} (hg : ∀ x, (starRingEnd ℂ) (g x) = g x) (s : ℂ) :
    laplaceTest g ((starRingEnd ℂ) s) = (starRingEnd ℂ) (laplaceTest g s) := by
  unfold laplaceTest
  rw [← integral_conj]
  congr 1
  funext x
  rw [map_mul, hg, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_sub, Complex.conj_ofReal, map_div₀, map_one, map_ofNat]

/-- **The four-member orbit of a real even profile is `4·Re(F_g(ρ)²)`.** -/
theorem orbitSum_eq {g : ℝ → ℂ} (hev : ∀ x, g (-x) = g x)
    (hre : ∀ x, (starRingEnd ℂ) (g x) = g x) (ρ : ℂ) :
    orbitSum g ρ = 4 * (((laplaceTest g ρ ^ 2).re : ℝ) : ℂ) := by
  have e1 : ∀ s, laplaceTest g (1 - (starRingEnd ℂ) s) = (starRingEnd ℂ) (laplaceTest g s) := by
    intro s; rw [laplaceTest_even hev, laplaceTest_conj hre]
  set F := laplaceTest g ρ with hF
  have h1 : orbitTerm g ρ = F ^ 2 := by
    unfold orbitTerm; rw [e1, Complex.conj_conj]; ring
  have h2 : orbitTerm g (1 - ρ) = F ^ 2 := by
    unfold orbitTerm
    rw [map_sub, map_one, sub_sub_cancel, laplaceTest_conj hre, Complex.conj_conj,
      laplaceTest_even hev]
    ring
  have h3 : orbitTerm g ((starRingEnd ℂ) ρ) = (starRingEnd ℂ) (F ^ 2) := by
    unfold orbitTerm
    rw [Complex.conj_conj, laplaceTest_even hev, laplaceTest_conj hre, map_pow]
    ring
  have h4 : orbitTerm g (1 - (starRingEnd ℂ) ρ) = (starRingEnd ℂ) (F ^ 2) := by
    unfold orbitTerm
    rw [e1, map_sub, map_one, Complex.conj_conj, sub_sub_cancel, map_pow]
    ring
  unfold orbitSum
  rw [h1, h2, h3, h4]
  have hc := Complex.add_conj (F ^ 2)
  push_cast at hc
  linear_combination 2 * hc

/-! ### The phase-aligned profile -/

/-- The phase-aligned profile `g(x) = cos(γ₀x)·ψ(x)`. -/
def modulated (γ₀ : ℝ) (ψ : ℝ → ℂ) (x : ℝ) : ℂ := (Real.cos (γ₀ * x) : ℂ) * ψ x

theorem modulated_even {ψ : ℝ → ℂ} (hψ : ∀ x, ψ (-x) = ψ x) (γ₀ : ℝ) :
    ∀ x, modulated γ₀ ψ (-x) = modulated γ₀ ψ x := by
  intro x; unfold modulated; rw [hψ, mul_neg, Real.cos_neg]

theorem modulated_real {ψ : ℝ → ℂ} (hψ : ∀ x, (starRingEnd ℂ) (ψ x) = ψ x) (γ₀ : ℝ) :
    ∀ x, (starRingEnd ℂ) (modulated γ₀ ψ x) = modulated γ₀ ψ x := by
  intro x; unfold modulated; rw [map_mul, Complex.conj_ofReal, hψ]

theorem modulated_continuous {ψ : ℝ → ℂ} (hψ : Continuous ψ) (γ₀ : ℝ) :
    Continuous (modulated γ₀ ψ) := by
  unfold modulated; fun_prop

theorem modulated_hasCompactSupport {ψ : ℝ → ℂ} (hψ : HasCompactSupport ψ) (γ₀ : ℝ) :
    HasCompactSupport (modulated γ₀ ψ) := by
  unfold modulated; exact hψ.mul_left

/-- **Phase alignment**: `F_g(s) = ½·F_ψ(s + iγ₀) + ½·F_ψ(s − iγ₀)`. -/
theorem laplaceTest_modulated {ψ : ℝ → ℂ} (hψ : Continuous ψ) (hs : HasCompactSupport ψ)
    (γ₀ : ℝ) (s : ℂ) :
    laplaceTest (modulated γ₀ ψ) s
      = (1 / 2 : ℂ) * laplaceTest ψ (s + γ₀ * I) + (1 / 2 : ℂ) * laplaceTest ψ (s - γ₀ * I) := by
  unfold laplaceTest modulated
  have hint1 := laplaceTest_integrand_integrable hψ hs (s + γ₀ * I)
  have hint2 := laplaceTest_integrand_integrable hψ hs (s - γ₀ * I)
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add (hint1.const_mul _) (hint2.const_mul _)]
  congr 1
  funext x
  have hcos : (Real.cos (γ₀ * x) : ℂ)
      = (Complex.exp (((γ₀ * x : ℝ) : ℂ) * I) + Complex.exp (-((γ₀ * x : ℝ) : ℂ) * I)) / 2 := by
    rw [Complex.ofReal_cos]
    have := Complex.two_cos (x := ((γ₀ * x : ℝ) : ℂ))
    linear_combination (1 / 2 : ℂ) * this
  have e1 : Complex.exp (((γ₀ * x : ℝ) : ℂ) * I) * Complex.exp ((s - 1 / 2) * x)
      = Complex.exp ((s + γ₀ * I - 1 / 2) * x) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  have e2 : Complex.exp (-((γ₀ * x : ℝ) : ℂ) * I) * Complex.exp ((s - 1 / 2) * x)
      = Complex.exp ((s - γ₀ * I - 1 / 2) * x) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [hcos]
  linear_combination (ψ x / 2) * e1 + (ψ x / 2) * e2

/-! ### The real member: `F_ψ(½ + δ) = ∫ ψ e^{δx}` and its mass lower bound -/

/-- At the real point `½ + δ`, `F_ψ` is the real integral `∫ ψ(x) e^{δx} dx`. -/
theorem laplaceTest_ofReal_re (ψ : ℝ → ℝ) (δ : ℝ) :
    laplaceTest (fun x => (ψ x : ℂ)) ((1 / 2 + δ : ℝ) : ℂ)
      = ((∫ x, ψ x * Real.exp (δ * x) : ℝ) : ℂ) := by
  unfold laplaceTest
  have h : ∀ x : ℝ, (fun x => (ψ x : ℂ)) x * Complex.exp ((((1 / 2 + δ : ℝ) : ℂ) - 1 / 2) * (x : ℂ))
      = ((ψ x * Real.exp (δ * x) : ℝ) : ℂ) := by
    intro x
    rw [show (((1 / 2 + δ : ℝ) : ℂ) - 1 / 2) * (x : ℂ) = ((δ * x : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_exp]
    push_cast
    ring
  simp_rw [h]
  exact integral_ofReal

/-- Mass lower bound: a nonnegative profile that is `≥ 1` on `[Λ−2, Λ−1]` has
`∫ ψ e^{δx} ≥ e^{δ(Λ−2)}` for `δ ≥ 0`. -/
theorem integral_mass_lower {ψ : ℝ → ℝ} (hψc : Continuous ψ) (hsupp : HasCompactSupport ψ)
    (hnn : ∀ x, 0 ≤ ψ x) {Λ δ : ℝ} (hδ : 0 ≤ δ)
    (hmass : ∀ x ∈ Set.Icc (Λ - 2) (Λ - 1), 1 ≤ ψ x) :
    Real.exp (δ * (Λ - 2)) ≤ ∫ x, ψ x * Real.exp (δ * x) := by
  have hint : Integrable (fun x => ψ x * Real.exp (δ * x)) :=
    (hψc.mul (by fun_prop)).integrable_of_hasCompactSupport hsupp.mul_right
  have hnn' : 0 ≤ᵐ[volume] fun x => ψ x * Real.exp (δ * x) :=
    Eventually.of_forall fun x => mul_nonneg (hnn x) (Real.exp_pos _).le
  have hvol : volume.real (Set.Icc (Λ - 2) (Λ - 1)) = 1 := by
    simp [measureReal_def, Real.volume_Icc]; norm_num
  have hpt : ∀ x ∈ Set.Icc (Λ - 2) (Λ - 1), Real.exp (δ * (Λ - 2)) ≤ ψ x * Real.exp (δ * x) := by
    intro x hx
    calc Real.exp (δ * (Λ - 2)) = 1 * Real.exp (δ * (Λ - 2)) := (one_mul _).symm
      _ ≤ ψ x * Real.exp (δ * x) :=
        mul_le_mul (hmass x hx) (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hx.1 hδ))
          (Real.exp_pos _).le (hnn x)
  have h1 := setIntegral_ge_of_const_le_real (μ := volume) (s := Set.Icc (Λ - 2) (Λ - 1))
    measurableSet_Icc (by simp) hpt hint.integrableOn
  rw [hvol, mul_one] at h1
  exact h1.trans (setIntegral_le_integral hint hnn')

/-! ### The off-resonant member: four integrations by parts -/

/-- Derivatives of a profile vanishing outside `|x| ≤ Λ` vanish there too. -/
theorem iterate_deriv_eq_zero_of_radius {ψ : ℝ → ℂ} {Λ : ℝ} (hR : ∀ x, Λ < |x| → ψ x = 0)
    (n : ℕ) : ∀ x, Λ < |x| → deriv^[n] ψ x = 0 := by
  induction n with
  | zero => exact hR
  | succ n ih =>
    intro x hx
    rw [Function.iterate_succ_apply']
    have hopen : IsOpen {y : ℝ | Λ < |y|} := isOpen_lt continuous_const continuous_abs
    have hev : deriv^[n] ψ =ᶠ[𝓝 x] fun _ => (0 : ℂ) := by
      filter_upwards [hopen.mem_nhds hx] with y hy using ih y hy
    rw [hev.deriv_eq, deriv_const]

/-- Off resonance, `‖F_ψ(½ + δ + iγ)‖ ≤ e^{δΛ}‖ψ''''‖₁ / γ⁴`. -/
theorem laplaceTest_off_bound {ψ : ℝ → ℂ} (hψ : ContDiff ℝ ∞ ψ) (hsupp : HasCompactSupport ψ)
    {Λ : ℝ} (hΛ : 0 ≤ Λ) (hR : ∀ x, Λ < |x| → ψ x = 0) {δ γ : ℝ} (hδ : 0 ≤ δ) (hγ : γ ≠ 0) :
    ‖laplaceTest ψ (((1 / 2 + δ : ℝ) : ℂ) + (γ : ℂ) * I)‖
      ≤ Real.exp (δ * Λ) * (∫ x, ‖deriv^[4] ψ x‖) / γ ^ 4 := by
  have hs : (((1 / 2 + δ : ℝ) : ℂ) + (γ : ℂ) * I) ≠ 1 / 2 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    exact hγ this
  rw [laplaceTest_eq_fourth_deriv hψ hsupp hs, norm_mul, norm_pow, norm_inv]
  have hb := laplaceTest_norm_le (hψ.iterate_deriv 4).continuous
    (hasCompactSupport_iterate_deriv hsupp 4) hΛ (iterate_deriv_eq_zero_of_radius hR 4) hδ
    (show |(1 / 2 + δ) - 1 / 2| ≤ δ by
      rw [show (1 / 2 + δ - 1 / 2 : ℝ) = δ by ring, abs_of_nonneg hδ]) γ
  have hnorm : |γ| ≤ ‖(((1 / 2 + δ : ℝ) : ℂ) + (γ : ℂ) * I) - 1 / 2‖ := by
    have := Complex.abs_im_le_norm ((((1 / 2 + δ : ℝ) : ℂ) + (γ : ℂ) * I) - 1 / 2)
    simpa using this
  have hγ4 : γ ^ 4 ≤ ‖(((1 / 2 + δ : ℝ) : ℂ) + (γ : ℂ) * I) - 1 / 2‖ ^ 4 := by
    calc γ ^ 4 = |γ| ^ 4 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
      _ ≤ _ := pow_le_pow_left₀ (abs_nonneg _) hnorm 4
  have hγ4pos : 0 < γ ^ 4 := by positivity
  have hpos : 0 < ‖(((1 / 2 + δ : ℝ) : ℂ) + (γ : ℂ) * I) - 1 / 2‖ ^ 4 := lt_of_lt_of_le hγ4pos hγ4
  calc ‖(((1 / 2 + δ : ℝ) : ℂ) + (γ : ℂ) * I) - 1 / 2‖⁻¹ ^ 4
        * ‖laplaceTest (deriv^[4] ψ) (((1 / 2 + δ : ℝ) : ℂ) + (γ : ℂ) * I)‖
      ≤ (γ ^ 4)⁻¹ * (Real.exp (δ * Λ) * ∫ x, ‖deriv^[4] ψ x‖) := by
        apply mul_le_mul _ hb (norm_nonneg _) (by positivity)
        rw [inv_pow]
        exact inv_anti₀ hγ4pos hγ4
    _ = Real.exp (δ * Λ) * (∫ x, ‖deriv^[4] ψ x‖) / γ ^ 4 := by ring

/-! ### The orbit's exponential type -/

/-- **Lower bound.**  For the phase-aligned bump profile and `γ₀⁴ ≥ ½e^{2δ}‖ψ''''‖₁`, the
four-member orbit of `ρ₀ = ½ + δ + iγ₀` satisfies `Re(orbit) ≥ ½·e^{2δ(Λ−2)}`. -/
theorem orbit_lower_bound {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ (fun x => (ψ x : ℂ)))
    (hsupp : HasCompactSupport (fun x => (ψ x : ℂ))) (hnn : ∀ x, 0 ≤ ψ x)
    (hev : ∀ x, ψ (-x) = ψ x) {Λ : ℝ} (hΛ : 2 ≤ Λ) (hR : ∀ x, Λ < |x| → ψ x = 0)
    (hmass : ∀ x ∈ Set.Icc (Λ - 2) (Λ - 1), 1 ≤ ψ x) {δ γ₀ : ℝ} (hδ : 0 ≤ δ) (hγ : 0 < γ₀)
    (hbig : Real.exp (2 * δ) * (∫ x, ‖deriv^[4] (fun x => (ψ x : ℂ)) x‖) ≤ 2 * γ₀ ^ 4) :
    Real.exp (2 * δ * (Λ - 2)) / 2
      ≤ (orbitSum (modulated γ₀ (fun x => (ψ x : ℂ)))
          (((1 / 2 + δ : ℝ) : ℂ) + (γ₀ : ℂ) * I)).re := by
  set ψc : ℝ → ℂ := fun x => (ψ x : ℂ) with hψc
  have hψcont : Continuous ψc := hψ.continuous
  have hψR : ∀ x, Λ < |x| → ψc x = 0 := fun x hx => by simp [hψc, hR x hx]
  have hevc : ∀ x, ψc (-x) = ψc x := fun x => by simp [hψc, hev]
  have hrec : ∀ x, (starRingEnd ℂ) (ψc x) = ψc x := fun x => by simp [hψc]
  have hΛ0 : 0 ≤ Λ := by linarith
  -- the orbit is 4 Re(F_g(ρ₀)²)
  rw [orbitSum_eq (modulated_even hevc γ₀) (modulated_real hrec γ₀)]
  -- phase alignment at ρ₀
  rw [laplaceTest_modulated hψcont hsupp γ₀]
  have hA : (((1 / 2 + δ : ℝ) : ℂ) + (γ₀ : ℂ) * I) - γ₀ * I = ((1 / 2 + δ : ℝ) : ℂ) := by ring
  have hB : (((1 / 2 + δ : ℝ) : ℂ) + (γ₀ : ℂ) * I) + γ₀ * I
      = ((1 / 2 + δ : ℝ) : ℂ) + ((2 * γ₀ : ℝ) : ℂ) * I := by push_cast; ring
  have hAval : laplaceTest ψc ((1 / 2 + δ : ℝ) : ℂ) = ((∫ x, ψ x * Real.exp (δ * x) : ℝ) : ℂ) :=
    laplaceTest_ofReal_re ψ δ
  rw [hA, hB, hAval]
  set a : ℝ := ∫ x, ψ x * Real.exp (δ * x) with ha
  set B : ℂ := laplaceTest ψc (((1 / 2 + δ : ℝ) : ℂ) + ((2 * γ₀ : ℝ) : ℂ) * I) with hBdef
  -- bounds on a and B
  have hψreal : Continuous ψ := by
    have := hψcont; exact Complex.continuous_re.comp this |>.congr (fun x => by simp [hψc])
  have hsuppr : HasCompactSupport ψ := by
    refine hsupp.mono fun x hx => ?_
    exact Complex.ofReal_ne_zero.mpr hx
  have ha_lb : Real.exp (δ * (Λ - 2)) ≤ a := integral_mass_lower hψreal hsuppr hnn hδ hmass
  have ha_pos : 0 < a := lt_of_lt_of_le (Real.exp_pos _) ha_lb
  have hB_bound : ‖B‖ ≤ Real.exp (δ * Λ) * (∫ x, ‖deriv^[4] ψc x‖) / (2 * γ₀) ^ 4 :=
    laplaceTest_off_bound hψ hsupp hΛ0 hψR hδ (by positivity)
  have hB_small : ‖B‖ ≤ a / 8 := by
    have hK : 0 ≤ ∫ x, ‖deriv^[4] ψc x‖ := integral_nonneg fun x => norm_nonneg _
    have h16 : (2 * γ₀) ^ 4 = 16 * γ₀ ^ 4 := by ring
    have hexp : Real.exp (δ * Λ) = Real.exp (2 * δ) * Real.exp (δ * (Λ - 2)) := by
      rw [← Real.exp_add]; congr 1; ring
    calc ‖B‖ ≤ Real.exp (δ * Λ) * (∫ x, ‖deriv^[4] ψc x‖) / (2 * γ₀) ^ 4 := hB_bound
      _ = Real.exp (δ * (Λ - 2)) * (Real.exp (2 * δ) * ∫ x, ‖deriv^[4] ψc x‖) / (16 * γ₀ ^ 4) := by
          rw [h16, hexp]; ring
      _ ≤ Real.exp (δ * (Λ - 2)) * (2 * γ₀ ^ 4) / (16 * γ₀ ^ 4) := by
          gcongr
      _ = Real.exp (δ * (Λ - 2)) / 8 := by field_simp; ring
      _ ≤ a / 8 := by linarith
  -- Re((½a + ½B)²)·4 = Re((a + B)²) ≥ a² − 2a‖B‖ − ‖B‖² ≥ a²/2
  have hre : (((1 / 2 : ℂ) * B + (1 / 2 : ℂ) * (a : ℂ)) ^ 2).re
      = (a ^ 2 + 2 * a * B.re + (B ^ 2).re) / 4 := by
    have : ((1 / 2 : ℂ) * B + (1 / 2 : ℂ) * (a : ℂ)) ^ 2
        = ((a : ℂ) ^ 2 + 2 * (a : ℂ) * B + B ^ 2) / 4 := by ring
    rw [this]
    simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, pow_two]
  have hBre : -‖B‖ ≤ B.re := by
    have := Complex.abs_re_le_norm B
    linarith [neg_abs_le B.re]
  have hB2re : -(‖B‖ ^ 2) ≤ (B ^ 2).re := by
    have := Complex.abs_re_le_norm (B ^ 2)
    rw [norm_pow] at this
    linarith [neg_abs_le (B ^ 2).re]
  have hnormB : 0 ≤ ‖B‖ := norm_nonneg _
  have key : a ^ 2 / 2 ≤ a ^ 2 + 2 * a * B.re + (B ^ 2).re := by
    nlinarith [hB_small, hBre, hB2re, ha_pos, hnormB]
  have hcast : (4 * (((((1 / 2 : ℂ) * B + (1 / 2 : ℂ) * (a : ℂ)) ^ 2).re : ℝ) : ℂ)).re
      = 4 * (((1 / 2 : ℂ) * B + (1 / 2 : ℂ) * (a : ℂ)) ^ 2).re := by simp
  rw [hcast, hre]
  have hsq : Real.exp (2 * δ * (Λ - 2)) ≤ a ^ 2 := by
    have : Real.exp (2 * δ * (Λ - 2)) = Real.exp (δ * (Λ - 2)) ^ 2 := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [this]
    exact pow_le_pow_left₀ (Real.exp_pos _).le ha_lb 2
  linarith

/-- **Upper bound.**  `Re(orbit) ≤ 4·(e^{δΛ}∫ψ)²`: the type is at most `2δ` per unit `Λ`. -/
theorem orbit_upper_bound {ψ : ℝ → ℝ} (hψc : Continuous ψ) (hsupp : HasCompactSupport ψ)
    (hnn : ∀ x, 0 ≤ ψ x) (hev : ∀ x, ψ (-x) = ψ x) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hR : ∀ x, Λ < |x| → ψ x = 0) {δ γ₀ : ℝ} (hδ : 0 ≤ δ) :
    (orbitSum (modulated γ₀ (fun x => (ψ x : ℂ))) (((1 / 2 + δ : ℝ) : ℂ) + (γ₀ : ℂ) * I)).re
      ≤ 4 * (Real.exp (δ * Λ) * ∫ x, ψ x) ^ 2 := by
  set ψc : ℝ → ℂ := fun x => (ψ x : ℂ) with hψcdef
  have hcont : Continuous ψc := by fun_prop
  have hsuppc : HasCompactSupport ψc := hsupp.comp_left Complex.ofReal_zero
  have hevc : ∀ x, ψc (-x) = ψc x := fun x => by simp [hψcdef, hev]
  have hrec : ∀ x, (starRingEnd ℂ) (ψc x) = ψc x := fun x => by simp [hψcdef]
  set g := modulated γ₀ ψc with hg
  have hgR : ∀ x, Λ < |x| → g x = 0 := fun x hx => by simp [hg, modulated, hψcdef, hR x hx]
  rw [orbitSum_eq (modulated_even hevc γ₀) (modulated_real hrec γ₀)]
  have hF := laplaceTest_norm_le (modulated_continuous hcont γ₀)
    (modulated_hasCompactSupport hsuppc γ₀) hΛ hgR hδ
    (show |(1 / 2 + δ) - 1 / 2| ≤ δ by
      rw [show (1 / 2 + δ - 1 / 2 : ℝ) = δ by ring, abs_of_nonneg hδ]) γ₀
  have hgint : ∫ x, ‖g x‖ ≤ ∫ x, ψ x := by
    have hint : Integrable ψ := hψc.integrable_of_hasCompactSupport hsupp
    have hint' : Integrable (fun x => ‖g x‖) :=
      ((modulated_continuous hcont γ₀).norm).integrable_of_hasCompactSupport
        ((modulated_hasCompactSupport hsuppc γ₀).norm)
    refine integral_mono hint' hint fun x => ?_
    simp only [hg, modulated, hψcdef, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hnn x)]
    calc |Real.cos (γ₀ * x)| * ψ x ≤ 1 * ψ x :=
          mul_le_mul_of_nonneg_right (Real.abs_cos_le_one _) (hnn x)
      _ = ψ x := one_mul _
  have hnormF : ‖laplaceTest g (((1 / 2 + δ : ℝ) : ℂ) + (γ₀ : ℂ) * I)‖
      ≤ Real.exp (δ * Λ) * ∫ x, ψ x := by
    calc _ ≤ Real.exp (δ * Λ) * ∫ x, ‖g x‖ := hF
      _ ≤ Real.exp (δ * Λ) * ∫ x, ψ x := by gcongr
  have hcast : (4 * ((((laplaceTest g (((1 / 2 + δ : ℝ) : ℂ) + (γ₀ : ℂ) * I)) ^ 2).re : ℝ) : ℂ)).re
      = 4 * ((laplaceTest g (((1 / 2 + δ : ℝ) : ℂ) + (γ₀ : ℂ) * I)) ^ 2).re := by simp
  rw [hcast]
  have h1 := Complex.abs_re_le_norm ((laplaceTest g (((1 / 2 + δ : ℝ) : ℂ) + (γ₀ : ℂ) * I)) ^ 2)
  rw [norm_pow] at h1
  have h2 : ‖laplaceTest g (((1 / 2 + δ : ℝ) : ℂ) + (γ₀ : ℂ) * I)‖ ^ 2
      ≤ (Real.exp (δ * Λ) * ∫ x, ψ x) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hnormF 2
  linarith [le_abs_self ((laplaceTest g (((1 / 2 + δ : ℝ) : ℂ) + (γ₀ : ℂ) * I) ^ 2).re)]

end CriticalLinePhasor.ContourArgument
