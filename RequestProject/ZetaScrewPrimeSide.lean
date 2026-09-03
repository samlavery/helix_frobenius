import RequestProject.ZetaScrewRamp

/-!
# The explicit formula in profile form, up to the Archimedean field (Track E)

Two compiled fields of Suzuki's Thm 1.1(2) — the ends (`endsProfile_laplace`) and the winding
ramp (`rampProfile_laplace`) — are assembled into the prime side `ends − winding`, and the zero
helix profile `Ψ` is compared with it:

* `primeSideProfile t = endsProfile t − rampProfile t`, `primeSideProfile_laplace`:
  `∫₀^∞ (ends − winding) e^{izt} = −z⁻²[1/s + 1/(s−1) − Σ Λ(n) n^{−s}]`, `s = ½ − iz`.
* `archRemainder t = Ψ(t) − primeSideProfile t`, **`archRemainder_laplace`**:
  `∫₀^∞ (Ψ − ends + winding)(t) e^{izt} dt = −z⁻²[½ Γ′/Γ(s/2) − ½ log π]` for `Im z > ½`.

So the zero helix minus the prime side has a transform with NO arithmetic content: the
Archimedean clock alone. This is the explicit formula in profile form with the third field
isolated as a statement about a compiled function; field 3 itself (the time-domain Archimedean
profile) needs the digamma partial-fraction series, absent from Mathlib (ledger 527).

Also: `integrableOn_tsum_of_summable_integral_norm` (a tsum with summable norm integrals is
integrable — the `L¹` argument of `CarrierThetaIdentification`, made generic), and the
integrability of `Ψ e^{izt}`, `R e^{izt}`, `ends · e^{izt}` on the half-line.

No `sorry`, no `axiom`.
-/

open Complex Filter Topology MeasureTheory ArithmeticFunction

noncomputable section

namespace CriticalLinePhasor.HilbertPolya

open CriticalLinePhasor.StBridge

/-- A countable sum of half-line-integrable functions with summable norm integrals is
integrable on the half-line (via `L¹`). -/
theorem integrableOn_tsum_of_summable_integral_norm {ι : Type*} [Countable ι] {F : ι → ℝ → ℂ}
    (hF_int : ∀ i, IntegrableOn (F i) (Set.Ioi 0) volume)
    (hF_sum : Summable fun i => ∫ t in Set.Ioi (0 : ℝ), ‖F i t‖) :
    IntegrableOn (fun t : ℝ => ∑' i, F i t) (Set.Ioi 0) volume := by
  let μ : Measure ℝ := volume.restrict (Set.Ioi 0)
  have hFint : ∀ i, Integrable (F i) μ := hF_int
  let fL1 : ι → Lp ℂ 1 μ := fun i => (hFint i).toL1 (F i)
  have hnormL1 : Summable fun i => ‖fL1 i‖ := by
    have heq : (fun i => ‖fL1 i‖) = fun i => ∫ t in Set.Ioi (0 : ℝ), ‖F i t‖ := by
      funext i
      change ‖(hFint i).toL1 (F i)‖ = ∫ t, ‖F i t‖ ∂μ
      exact L1.norm_of_fun_eq_integral_norm (hFint i)
    rw [heq]
    exact hF_sum
  have henorm : ∑' i, ‖fL1 i‖ₑ ≠ ⊤ := tsum_enorm_ne_top_iff_summable_norm.mpr hnormL1
  have hcoeEach : ∀ᵐ x ∂μ, ∀ i, fL1 i x = F i x := by
    rw [ae_all_iff]
    intro i
    exact (hFint i).coeFn_toL1
  have hcoeSum : (fun x => (∑' i, fL1 i) x) =ᵐ[μ] fun x => ∑' i, F i x := by
    filter_upwards [Lp.coeFn_tsum henorm, hcoeEach] with x hxsum hxeach
    rw [hxsum]
    exact tsum_congr (fun i => hxeach i)
  exact (L1.integrable_coeFn (∑' i, fL1 i)).congr hcoeSum

/-! ## Integrability of the three profiles against `e^{izt}` -/

theorem endsProfile_mul_exp_integrable {z : ℂ} (hz : 1 / 2 < z.im) :
    IntegrableOn (fun t : ℝ => endsProfile t * Complex.exp (Complex.I * z * t))
      (Set.Ioi 0) volume := by
  have ha₁ : (Complex.I * z + 1 / 2).re < 0 := by
    rw [Complex.add_re, I_mul_re_neg]
    norm_num
    linarith
  have ha₂ : (Complex.I * z - 1 / 2).re < 0 := by
    rw [Complex.sub_re, I_mul_re_neg]
    norm_num
    linarith
  have ha₃ : (Complex.I * z).re < 0 := by
    rw [I_mul_re_neg]
    linarith
  have hfun : (fun t : ℝ => endsProfile t * Complex.exp (Complex.I * z * t))
      = fun t : ℝ => 4 * (Complex.exp ((Complex.I * z + 1 / 2) * t)
          + Complex.exp ((Complex.I * z - 1 / 2) * t)
          - 2 * Complex.exp ((Complex.I * z) * t)) := by
    funext t
    exact endsProfile_mul_exp_eq z t
  rw [hfun]
  exact (((integrableOn_exp_mul_complex_Ioi ha₁ 0).add
    (integrableOn_exp_mul_complex_Ioi ha₂ 0)).sub
      ((integrableOn_exp_mul_complex_Ioi ha₃ 0).const_mul 2)).const_mul 4

theorem rampProfile_mul_exp_integrable {z : ℂ} (hz : 1 / 2 < z.im) :
    IntegrableOn (fun t : ℝ => rampProfile t * Complex.exp (Complex.I * z * t))
      (Set.Ioi 0) volume := by
  have hb : 0 < z.im := by linarith
  have hpt : (fun t : ℝ => rampProfile t * Complex.exp (Complex.I * z * t))
      = fun t : ℝ => ∑' n : ℕ, rampTerm t n * Complex.exp (Complex.I * z * t) := by
    funext t
    unfold rampProfile
    rw [tsum_mul_right]
  rw [hpt]
  exact integrableOn_tsum_of_summable_integral_norm
    (fun n => rampTerm_mul_exp_integrable hb n) (rampTerm_integral_norm_summable hz)

theorem zetaScrew_mul_exp_integrable {z : ℂ} (hz : 1 / 2 < z.im) :
    IntegrableOn (fun t : ℝ => zetaScrew t * Complex.exp (Complex.I * z * t))
      (Set.Ioi 0) volume := by
  have hpt : (fun t : ℝ => zetaScrew t * Complex.exp (Complex.I * z * t))
      = fun t : ℝ => ∑' ρ : Zeros, screwTerm t ρ * Complex.exp (Complex.I * z * t) := by
    funext t
    unfold zetaScrew
    rw [tsum_mul_right]
  rw [hpt]
  exact integrableOn_tsum_of_summable_integral_norm
    (fun ρ => screwTerm_mul_exp_integrable hz ρ) (screwTerm_integral_norm_summable hz)

/-! ## The prime side and the Archimedean remainder -/

/-- The prime-side profile `ends − winding` (Suzuki (1.1), fields 1 and 2). -/
def primeSideProfile (t : ℝ) : ℂ := endsProfile t - rampProfile t

theorem primeSideProfile_mul_exp_eq (z : ℂ) (t : ℝ) :
    primeSideProfile t * Complex.exp (Complex.I * z * t)
      = endsProfile t * Complex.exp (Complex.I * z * t)
        - rampProfile t * Complex.exp (Complex.I * z * t) := by
  unfold primeSideProfile
  ring

theorem primeSideProfile_mul_exp_integrable {z : ℂ} (hz : 1 / 2 < z.im) :
    IntegrableOn (fun t : ℝ => primeSideProfile t * Complex.exp (Complex.I * z * t))
      (Set.Ioi 0) volume := by
  have h : (fun t : ℝ => primeSideProfile t * Complex.exp (Complex.I * z * t))
      = fun t : ℝ => endsProfile t * Complex.exp (Complex.I * z * t)
          - rampProfile t * Complex.exp (Complex.I * z * t) := by
    funext t
    exact primeSideProfile_mul_exp_eq z t
  rw [h]
  exact (endsProfile_mul_exp_integrable hz).sub (rampProfile_mul_exp_integrable hz)

/-- **The prime side's transform**: poles minus the von Mangoldt series, `s = ½ − iz`. -/
theorem primeSideProfile_laplace {z : ℂ} (hz : 1 / 2 < z.im) :
    ∫ t in Set.Ioi (0 : ℝ), primeSideProfile t * Complex.exp (Complex.I * z * t)
      = -(1 / z ^ 2) * (1 / (1 / 2 - Complex.I * z) + 1 / ((1 / 2 - Complex.I * z) - 1)
          - LSeries (fun n => ((Λ n : ℝ) : ℂ)) (1 / 2 - Complex.I * z)) := by
  have h : (fun t : ℝ => primeSideProfile t * Complex.exp (Complex.I * z * t))
      = fun t : ℝ => endsProfile t * Complex.exp (Complex.I * z * t)
          - rampProfile t * Complex.exp (Complex.I * z * t) := by
    funext t
    exact primeSideProfile_mul_exp_eq z t
  rw [h, integral_sub (endsProfile_mul_exp_integrable hz) (rampProfile_mul_exp_integrable hz),
    endsProfile_laplace hz, rampProfile_laplace hz]
  ring

/-- The Archimedean remainder `Ψ − (ends − winding)`. -/
def archRemainder (t : ℝ) : ℂ := zetaScrew t - primeSideProfile t

/-- **The explicit formula in profile form, up to the Archimedean field**: for `Im z > ½` and
`s = ½ − iz`, `∫₀^∞ (Ψ − ends + winding)(t) e^{izt} dt = −z⁻²[½ Γ′/Γ(s/2) − ½ log π]`.
The zero helix minus the prime side has no arithmetic content in its transform. -/
theorem archRemainder_laplace {z : ℂ} (hz : 1 / 2 < z.im) :
    ∫ t in Set.Ioi (0 : ℝ), archRemainder t * Complex.exp (Complex.I * z * t)
      = -(1 / z ^ 2) * (logDeriv Complex.Gamma ((1 / 2 - Complex.I * z) / 2) / 2
          - ((Real.log Real.pi : ℝ) : ℂ) / 2) := by
  have h : (fun t : ℝ => archRemainder t * Complex.exp (Complex.I * z * t))
      = fun t : ℝ => zetaScrew t * Complex.exp (Complex.I * z * t)
          - primeSideProfile t * Complex.exp (Complex.I * z * t) := by
    funext t
    unfold archRemainder
    ring
  rw [h, integral_sub (zetaScrew_mul_exp_integrable hz) (primeSideProfile_mul_exp_integrable hz),
    zetaScrew_fourier_arith hz, primeSideProfile_laplace hz]
  ring

end CriticalLinePhasor.HilbertPolya

#print axioms CriticalLinePhasor.HilbertPolya.integrableOn_tsum_of_summable_integral_norm
#print axioms CriticalLinePhasor.HilbertPolya.zetaScrew_mul_exp_integrable
#print axioms CriticalLinePhasor.HilbertPolya.primeSideProfile_laplace
#print axioms CriticalLinePhasor.HilbertPolya.archRemainder_laplace
