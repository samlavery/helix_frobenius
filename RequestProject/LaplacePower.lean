import Mathlib

/-!
# The complex Laplace transform of powers (ledger 605, Draft B, first brick)

`∫₀^∞ u^m e^{−su} du = m!/s^{m+1}` for `Re s > 0`. This is the bridge from the pole jets of the door
(595: `(−1)^m m! s^{−m−1}`) to the ℓ-variable of the prime symbol (596): the DC's pole part becomes
the Laplace transform of the symbol, so the door reads as one functional of the symbol in one
variable — Weil's ℓ-form. Integrability by domination (`u^m e^{−σu/2}` bounded), recursion by the
improper fundamental theorem of calculus.
-/

open Complex MeasureTheory Set Filter Topology

namespace CriticalLinePhasor.ContourArgument

/-- `v^m e^{−v}` is bounded on `[0, ∞)`. -/
theorem pow_mul_exp_neg_bddAbove (m : ℕ) :
    ∃ K : ℝ, ∀ v : ℝ, 0 ≤ v → v ^ m * Real.exp (-v) ≤ K := by
  have ht := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero m
  obtain ⟨T, hT⟩ := eventually_atTop.1 (ht.eventually_lt_const (by norm_num : (0:ℝ) < 1))
  obtain ⟨K₀, hK₀⟩ := (isCompact_Icc (a := (0:ℝ)) (b := T)).exists_bound_of_continuousOn
    (by fun_prop : ContinuousOn (fun v : ℝ => v ^ m * Real.exp (-v)) (Icc 0 T))
  refine ⟨max K₀ 1, fun v hv => ?_⟩
  by_cases hvT : v ≤ T
  · have := hK₀ v ⟨hv, hvT⟩
    rw [Real.norm_eq_abs] at this
    exact (le_abs_self _).trans (this.trans (le_max_left _ _))
  · exact (hT v (by linarith)).le.trans (le_max_right _ _)

/-- `u^m e^{−σu/2}` is bounded on `[0, ∞)` for `σ > 0`. -/
theorem pow_mul_exp_neg_half_bounded (m : ℕ) {σ : ℝ} (hσ : 0 < σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, 0 ≤ u → u ^ m * Real.exp (-(σ / 2 * u)) ≤ C := by
  obtain ⟨K, hK⟩ := pow_mul_exp_neg_bddAbove m
  have hK0 : 0 ≤ K := le_trans (by simp) (hK 0 le_rfl)
  refine ⟨(2 / σ) ^ m * K, by positivity, fun u hu => ?_⟩
  have hv : 0 ≤ σ / 2 * u := by positivity
  have hu' : u ^ m = (2 / σ) ^ m * (σ / 2 * u) ^ m := by
    rw [← mul_pow]
    congr 1
    field_simp
  calc u ^ m * Real.exp (-(σ / 2 * u))
      = (2 / σ) ^ m * ((σ / 2 * u) ^ m * Real.exp (-(σ / 2 * u))) := by rw [hu']; ring
    _ ≤ (2 / σ) ^ m * K := mul_le_mul_of_nonneg_left (hK _ hv) (by positivity)

/-- The norm of `u^m e^{−su}` for `u ≥ 0`. -/
theorem norm_pow_mul_cexp {s : ℂ} {u : ℝ} (hu : 0 ≤ u) (m : ℕ) :
    ‖(u : ℂ) ^ m * Complex.exp (-(s * u))‖ = u ^ m * Real.exp (-(s.re * u)) := by
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu, Complex.norm_exp]
  congr 2
  simp [Complex.mul_re]

/-- Integrability of `u^m e^{−su}` on `(0, ∞)` for `Re s > 0`. -/
theorem integrableOn_pow_mul_cexp (m : ℕ) {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun u : ℝ => (u : ℂ) ^ m * Complex.exp (-(s * u))) (Ioi 0) := by
  obtain ⟨C, hC0, hC⟩ := pow_mul_exp_neg_half_bounded m hs
  have hg : IntegrableOn (fun u : ℝ => C * ‖Complex.exp ((-(s.re / 2) : ℂ) * u)‖) (Ioi 0) :=
    ((integrableOn_exp_mul_complex_Ioi (a := (-(s.re / 2) : ℂ)) (by simp; linarith) 0).norm).const_mul C
  refine hg.mono' ?_ ?_
  · exact (by fun_prop : Continuous (fun u : ℝ => (u : ℂ) ^ m * Complex.exp (-(s * u)))).aestronglyMeasurable
  · rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall (fun u hu => ?_)
    have hu0 : 0 ≤ u := le_of_lt hu
    rw [norm_pow_mul_cexp hu0, Complex.norm_exp]
    have hre : ((-(s.re / 2) : ℂ) * (u : ℂ)).re = -(s.re / 2 * u) := by
      simp [Complex.mul_re]
    rw [hre]
    have hsplit : Real.exp (-(s.re * u)) = Real.exp (-(s.re / 2 * u)) * Real.exp (-(s.re / 2 * u)) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [hsplit, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hC u hu0) (Real.exp_pos _).le

/-- The Laplace integrand tends to zero. -/
theorem tendsto_pow_mul_cexp {s : ℂ} (hs : 0 < s.re) (m : ℕ) :
    Tendsto (fun u : ℝ => (u : ℂ) ^ m * Complex.exp (-(s * u))) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h1 : Tendsto (fun u : ℝ => (s.re * u) ^ m * Real.exp (-(s.re * u))) atTop (𝓝 0) :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero m).comp (tendsto_id.const_mul_atTop hs)
  have h2 : Tendsto (fun u : ℝ => (1 / s.re) ^ m * ((s.re * u) ^ m * Real.exp (-(s.re * u))))
      atTop (𝓝 0) := by
    simpa using h1.const_mul ((1 / s.re) ^ m)
  refine (h2.congr' ?_)
  filter_upwards [eventually_ge_atTop (0:ℝ)] with u hu
  rw [norm_pow_mul_cexp hu]
  have : (1 / s.re) ^ m * (s.re * u) ^ m = u ^ m := by
    rw [← mul_pow]; congr 1; field_simp
  rw [← mul_assoc, this]

/-- **The Laplace transform of `u^m`:** `∫₀^∞ u^m e^{−su} du = m!/s^{m+1}` for `Re s > 0`. -/
theorem laplace_pow {s : ℂ} (hs : 0 < s.re) (m : ℕ) :
    ∫ u in Ioi (0:ℝ), (u : ℂ) ^ m * Complex.exp (-(s * u)) = (m.factorial : ℂ) / s ^ (m + 1) := by
  have hs0 : s ≠ 0 := fun h => by rw [h] at hs; simp at hs
  induction m with
  | zero =>
    simp only [pow_zero, one_mul, Nat.factorial_zero, Nat.cast_one, zero_add, pow_one]
    have := integral_exp_mul_complex_Ioi (a := -s) (by simp; linarith) 0
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero] at this
    have e : (fun u : ℝ => Complex.exp (-(s * u))) = fun u : ℝ => Complex.exp (-s * u) := by
      funext u; ring_nf
    rw [e, this]
    field_simp
  | succ m ih =>
    -- f(u) = −u^(m+1) e^{−su}/s ; f' = u^(m+1) e^{−su} − ((m+1)/s) u^m e^{−su}
    have hderiv : ∀ u : ℝ, HasDerivAt (fun u : ℝ => -((u : ℂ) ^ (m + 1) * Complex.exp (-(s * u))) / s)
        ((u : ℂ) ^ (m + 1) * Complex.exp (-(s * u))
          - ((m + 1 : ℂ) / s) * ((u : ℂ) ^ m * Complex.exp (-(s * u)))) u := by
      intro u
      have hp : HasDerivAt (fun u : ℝ => (u : ℂ) ^ (m + 1))
          (((m + 1 : ℕ) : ℂ) * (u : ℂ) ^ (m + 1 - 1) * 1) u :=
        (hasDerivAt_id u).ofReal_comp.pow (m + 1)
      have h1 : HasDerivAt (fun u : ℝ => -(s * (u : ℂ))) (-(s * 1)) u :=
        ((hasDerivAt_id u).ofReal_comp.const_mul s).neg
      have he : HasDerivAt (fun u : ℝ => Complex.exp (-(s * u)))
          (Complex.exp (-(s * u)) * (-(s * 1))) u := h1.cexp
      have hd := ((hp.mul he).neg).div_const s
      refine hd.congr_deriv ?_
      simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, mul_one]
      field_simp
      ring
    set f : ℝ → ℂ := fun u => -((u : ℂ) ^ (m + 1) * Complex.exp (-(s * u))) / s with hf
    have hcont : ContinuousWithinAt f (Ici 0) 0 := (hderiv 0).continuousAt.continuousWithinAt
    have hlim : Tendsto f atTop (𝓝 0) := by
      have := (tendsto_pow_mul_cexp hs (m + 1)).neg.div_const s
      simpa [hf] using this
    have hint : IntegrableOn (fun u : ℝ => (u : ℂ) ^ (m + 1) * Complex.exp (-(s * u))
        - ((m + 1 : ℂ) / s) * ((u : ℂ) ^ m * Complex.exp (-(s * u)))) (Ioi 0) :=
      (integrableOn_pow_mul_cexp (m + 1) hs).sub ((integrableOn_pow_mul_cexp m hs).const_mul _)
    have hftc := integral_Ioi_of_hasDerivAt_of_tendsto hcont (fun u _ => hderiv u) hint hlim
    have hf0 : f 0 = 0 := by simp [hf]
    rw [hf0, sub_zero] at hftc
    rw [integral_sub (integrableOn_pow_mul_cexp (m + 1) hs) ((integrableOn_pow_mul_cexp m hs).const_mul _),
      integral_const_mul, ih] at hftc
    have hkey : ∫ u in Ioi (0:ℝ), (u : ℂ) ^ (m + 1) * Complex.exp (-(s * u))
        = ((m + 1 : ℂ) / s) * ((m.factorial : ℂ) / s ^ (m + 1)) := by
      linear_combination hftc
    rw [hkey, Nat.factorial_succ]
    push_cast
    field_simp
    ring

end CriticalLinePhasor.ContourArgument

#print axioms CriticalLinePhasor.ContourArgument.integrableOn_pow_mul_cexp
#print axioms CriticalLinePhasor.ContourArgument.laplace_pow
