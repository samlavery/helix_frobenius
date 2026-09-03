import RequestProject.ZetaScrewArithmetic

/-!
# The winding ramp and its transform (Track E, Suzuki Thm 1.1(2), field 2 of 3)

The prime side of the helix profile is the kinked ramp
`R(t) = Σ_{n ≤ e^t} Λ(n) n^{−½} (t − log n) = Σ_n Λ(n) n^{−½} (t − log n)₊`
(Suzuki (1.1), second field): one kink per prime power, at the helix time `log n`, of weight
`Λ(n)/√n` — the winding of the fiber's bank read on the carrier's own clock.

* `kink n t = (t − log n)₊`, `windingWeight n = Λ(n) n^{−½}`, `rampTerm`, `rampProfile`.
* `kink_laplace` — `∫₀^∞ (t − log n)₊ e^{izt} dt = −z⁻² e^{iz log n}` (`Im z > 0`, `n ≥ 1`): the
  integral starts at the kink; half-line FTC with antiderivative
  `e^{izt}((t − log n)/(iz) − (iz)⁻²)`.
* `windingWeight_mul_exp_log` — `Λ(n) n^{−½} e^{iz log n} = Λ(n) n^{−s}`, `s = ½ − iz`: the kink's
  transform IS the Dirichlet-series term (`LSeries.term`).
* **`rampProfile_laplace`** — for `Im z > ½`,
  `∫₀^∞ R(t) e^{izt} dt = −z⁻² · Σ_n Λ(n) n^{−s}`, `s = ½ − iz`.
  Fubini via the exact norm integrals `rampTerm_integral_norm` (`= z_im⁻² Λ(n) n^{−(½ + Im z)}`)
  and `LSeriesSummable_vonMangoldt` at the real abscissa `½ + Im z > 1`.

Harmonic line: scale = helix time `t = log(height)`; the ramp is the AC (winding) part of Ψ, its
transform is evaluated EXACTLY, kink by kink; the only estimate is the Fubini majorant, and it
is the Dirichlet series itself at a real point. Difficulty on the carrier (the kinks sit at the
prime clocks `log p^k`); none in the chart.

No `sorry`, no `axiom`.
-/

open Complex Filter Topology MeasureTheory ArithmeticFunction

noncomputable section

namespace CriticalLinePhasor.HilbertPolya

open CriticalLinePhasor.StBridge

/-! ## The kinked ramp -/

/-- The kink at helix time `log n`: `(t − log n)₊`. -/
def kink (n : ℕ) (t : ℝ) : ℝ := max (t - Real.log n) 0

/-- The winding weight `Λ(n) n^{−½}`. -/
def windingWeight (n : ℕ) : ℂ := ((Λ n : ℝ) : ℂ) * (n : ℂ) ^ (((-(1 / 2 : ℝ)) : ℝ) : ℂ)

/-- One kink of the winding ramp. -/
def rampTerm (t : ℝ) (n : ℕ) : ℂ := windingWeight n * (kink n t : ℂ)

/-- The winding ramp `Σ_{n ≤ e^t} Λ(n) n^{−½} (t − log n)` (Suzuki (1.1), second field). -/
def rampProfile (t : ℝ) : ℂ := ∑' n : ℕ, rampTerm t n

theorem kink_nonneg (n : ℕ) (t : ℝ) : 0 ≤ kink n t := le_max_right _ _

theorem log_natCast_nonneg {n : ℕ} (hn : 0 < n) : 0 ≤ Real.log n :=
  Real.log_nonneg (by exact_mod_cast hn)

theorem kink_le_self {n : ℕ} (hn : 0 < n) {t : ℝ} (ht : 0 ≤ t) : kink n t ≤ t := by
  have := log_natCast_nonneg hn
  unfold kink
  exact max_le (by linarith) ht

theorem kink_eq_zero_of_le {n : ℕ} {t : ℝ} (ht : t ≤ Real.log n) : kink n t = 0 := by
  unfold kink
  exact max_eq_right (by linarith)

theorem kink_eq_of_ge {n : ℕ} {t : ℝ} (ht : Real.log n ≤ t) : kink n t = t - Real.log n := by
  unfold kink
  exact max_eq_left (by linarith)

/-- `‖e^{izt}‖ = e^{−Im z · t}`. -/
theorem norm_exp_I_mul_ofReal (z : ℂ) (t : ℝ) :
    ‖Complex.exp (Complex.I * z * t)‖ = Real.exp (-z.im * t) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

/-! ## Integrability of one kink -/

/-- `(t − log n)₊ e^{izt}` is integrable on the half-line (`Im z > 0`), majorant
`(2/Im z) e^{−(Im z/2) t}` from `x e^{−x} ≤ 1`. -/
theorem kink_mul_exp_integrable {z : ℂ} (hz : 0 < z.im) {n : ℕ} (hn : 0 < n) :
    IntegrableOn (fun t : ℝ => (kink n t : ℂ) * Complex.exp (Complex.I * z * t))
      (Set.Ioi 0) volume := by
  have hb2 : 0 < z.im / 2 := by positivity
  have hg : IntegrableOn (fun t : ℝ => (2 / z.im) * Real.exp (-(z.im / 2) * t))
      (Set.Ioi 0) volume :=
    (integrableOn_exp_neg_mul_Ioi_zero hb2).const_mul _
  have hk : Continuous (fun t : ℝ => kink n t) :=
    (continuous_id.sub continuous_const).max continuous_const
  have hcont : Continuous (fun t : ℝ => (kink n t : ℂ) * Complex.exp (Complex.I * z * t)) :=
    (Complex.continuous_ofReal.comp hk).mul
      (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))
  refine Integrable.mono' hg hcont.aestronglyMeasurable.restrict ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  show ‖(kink n t : ℂ) * Complex.exp (Complex.I * z * t)‖
      ≤ (2 / z.im) * Real.exp (-(z.im / 2) * t)
  have ht0 : 0 ≤ t := le_of_lt ht
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (kink_nonneg n t),
    norm_exp_I_mul_ofReal]
  have h1 : kink n t ≤ t := kink_le_self hn ht0
  have hxe : (z.im / 2 * t) * Real.exp (-(z.im / 2 * t)) ≤ 1 := by
    have h := Real.add_one_le_exp (z.im / 2 * t)
    have hex : 0 < Real.exp (z.im / 2 * t) := Real.exp_pos _
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one hex]
    linarith
  have hsplit : Real.exp (-z.im * t)
      = Real.exp (-(z.im / 2 * t)) * Real.exp (-(z.im / 2 * t)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hzne : z.im ≠ 0 := hz.ne'
  calc kink n t * Real.exp (-z.im * t)
      ≤ t * Real.exp (-z.im * t) := mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = (2 / z.im) * ((z.im / 2 * t) * Real.exp (-(z.im / 2 * t)))
          * Real.exp (-(z.im / 2 * t)) := by
        rw [hsplit]
        field_simp
    _ ≤ (2 / z.im) * 1 * Real.exp (-(z.im / 2 * t)) := by gcongr
    _ = (2 / z.im) * Real.exp (-(z.im / 2) * t) := by
        rw [mul_one]
        congr 2
        ring

/-! ## The antiderivative of `(t − c) e^{izt}` on the half-line -/

/-- `d/dt [e^{izt}((t − c)/(iz) − (iz)⁻²)] = (t − c) e^{izt}`. -/
theorem kinkAnti_hasDerivAt {z : ℂ} (hz : z ≠ 0) (c : ℝ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.exp (Complex.I * z * t)
        * (((t : ℂ) - c) / (Complex.I * z) - 1 / (Complex.I * z) ^ 2))
      (((t : ℂ) - c) * Complex.exp (Complex.I * z * t)) t := by
  have hIz : Complex.I * z ≠ 0 := mul_ne_zero Complex.I_ne_zero hz
  have hE : HasDerivAt (fun t : ℝ => Complex.exp (Complex.I * z * t))
      (Complex.exp (Complex.I * z * t) * (Complex.I * z)) t := by
    have h := ((hasDerivAt_id (t : ℂ)).const_mul (Complex.I * z)).cexp
    exact h.comp_ofReal.congr_deriv (by simp)
  have hL : HasDerivAt (fun t : ℝ => ((t : ℂ) - c) / (Complex.I * z) - 1 / (Complex.I * z) ^ 2)
      (1 / (Complex.I * z)) t := by
    have h0 : HasDerivAt (fun t : ℝ => ((t : ℝ) : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
    exact ((h0.sub_const (c : ℂ)).div_const (Complex.I * z)).sub_const _
  refine (hE.mul hL).congr_deriv ?_
  field_simp
  ring

/-- The antiderivative tends to `0` at `+∞` when `Im z > 0`. -/
theorem kinkAnti_tendsto {z : ℂ} (hz : 0 < z.im) (c : ℝ) :
    Tendsto (fun t : ℝ => Complex.exp (Complex.I * z * t)
        * (((t : ℂ) - c) / (Complex.I * z) - 1 / (Complex.I * z) ^ 2)) atTop (𝓝 0) := by
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, Complex.zero_im] at hz
    exact lt_irrefl _ hz
  have h1 : Tendsto (fun t : ℝ => t ^ (1 : ℝ) * Real.exp (-z.im * t)) atTop (𝓝 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 z.im hz
  have h0 : Tendsto (fun t : ℝ => t ^ (0 : ℝ) * Real.exp (-z.im * t)) atTop (𝓝 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 z.im hz
  have hg : Tendsto (fun t : ℝ => (t ^ (1 : ℝ) * Real.exp (-z.im * t)) * (1 / ‖z‖)
      + (t ^ (0 : ℝ) * Real.exp (-z.im * t)) * (|c| / ‖z‖ + 1 / ‖z‖ ^ 2)) atTop (𝓝 0) := by
    have := (h1.mul_const (1 / ‖z‖)).add (h0.mul_const (|c| / ‖z‖ + 1 / ‖z‖ ^ 2))
    rwa [zero_mul, zero_mul, add_zero] at this
  refine squeeze_zero_norm' ?_ hg
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  show ‖Complex.exp (Complex.I * z * t)
        * (((t : ℂ) - c) / (Complex.I * z) - 1 / (Complex.I * z) ^ 2)‖
      ≤ (t ^ (1 : ℝ) * Real.exp (-z.im * t)) * (1 / ‖z‖)
        + (t ^ (0 : ℝ) * Real.exp (-z.im * t)) * (|c| / ‖z‖ + 1 / ‖z‖ ^ 2)
  rw [norm_mul, norm_exp_I_mul_ofReal, Real.rpow_one, Real.rpow_zero, one_mul]
  have hIznorm : ‖Complex.I * z‖ = ‖z‖ := by rw [norm_mul, Complex.norm_I, one_mul]
  have hA : ‖((t : ℂ) - c) / (Complex.I * z) - 1 / (Complex.I * z) ^ 2‖
      ≤ (t + |c|) / ‖z‖ + 1 / ‖z‖ ^ 2 := by
    calc ‖((t : ℂ) - c) / (Complex.I * z) - 1 / (Complex.I * z) ^ 2‖
        ≤ ‖((t : ℂ) - c) / (Complex.I * z)‖ + ‖1 / (Complex.I * z) ^ 2‖ := norm_sub_le _ _
      _ = ‖(t : ℂ) - c‖ / ‖z‖ + 1 / ‖z‖ ^ 2 := by
          rw [norm_div, norm_div, norm_pow, hIznorm, norm_one]
      _ ≤ (t + |c|) / ‖z‖ + 1 / ‖z‖ ^ 2 := by
          gcongr
          calc ‖(t : ℂ) - c‖ ≤ ‖(t : ℂ)‖ + ‖(c : ℂ)‖ := norm_sub_le _ _
            _ = |t| + |c| := by
                rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
            _ = t + |c| := by rw [abs_of_nonneg ht]
  calc Real.exp (-z.im * t) * ‖((t : ℂ) - c) / (Complex.I * z) - 1 / (Complex.I * z) ^ 2‖
      ≤ Real.exp (-z.im * t) * ((t + |c|) / ‖z‖ + 1 / ‖z‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hA (Real.exp_pos _).le
    _ = t * Real.exp (-z.im * t) * (1 / ‖z‖)
          + Real.exp (-z.im * t) * (|c| / ‖z‖ + 1 / ‖z‖ ^ 2) := by ring

/-! ## The transform of one kink -/

/-- **One kink's transform**: `∫₀^∞ (t − log n)₊ e^{izt} dt = −z⁻² e^{iz log n}` (`Im z > 0`). -/
theorem kink_laplace {z : ℂ} (hz : 0 < z.im) {n : ℕ} (hn : 0 < n) :
    ∫ t in Set.Ioi (0 : ℝ), (kink n t : ℂ) * Complex.exp (Complex.I * z * t)
      = -(1 / z ^ 2) * Complex.exp (Complex.I * z * Real.log n) := by
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, Complex.zero_im] at hz
    exact lt_irrefl _ hz
  have hlog : 0 ≤ Real.log n := log_natCast_nonneg hn
  -- the integrand vanishes before the kink
  have hrestr : ∫ t in Set.Ioi (0 : ℝ), (kink n t : ℂ) * Complex.exp (Complex.I * z * t)
      = ∫ t in Set.Ioi (Real.log n), (kink n t : ℂ) * Complex.exp (Complex.I * z * t) := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      (Set.Ioi_subset_Ioi hlog)
    intro x hx
    have hx2 : x ≤ Real.log n := not_lt.mp hx.2
    show (kink n x : ℂ) * Complex.exp (Complex.I * z * x) = 0
    rw [kink_eq_zero_of_le hx2, Complex.ofReal_zero, zero_mul]
  -- past the kink it is `(t − log n) e^{izt}`
  have hcongr : ∫ t in Set.Ioi (Real.log n), (kink n t : ℂ) * Complex.exp (Complex.I * z * t)
      = ∫ t in Set.Ioi (Real.log n),
          ((t : ℂ) - Real.log n) * Complex.exp (Complex.I * z * t) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    show (kink n t : ℂ) * Complex.exp (Complex.I * z * t)
      = ((t : ℂ) - Real.log n) * Complex.exp (Complex.I * z * t)
    rw [kink_eq_of_ge (le_of_lt ht), Complex.ofReal_sub]
  have hint : IntegrableOn (fun t : ℝ => ((t : ℂ) - Real.log n) * Complex.exp (Complex.I * z * t))
      (Set.Ioi (Real.log n)) volume := by
    have h := (kink_mul_exp_integrable hz hn).mono_set (Set.Ioi_subset_Ioi hlog)
    refine h.congr_fun ?_ measurableSet_Ioi
    intro t ht
    show (kink n t : ℂ) * Complex.exp (Complex.I * z * t)
      = ((t : ℂ) - Real.log n) * Complex.exp (Complex.I * z * t)
    rw [kink_eq_of_ge (le_of_lt ht), Complex.ofReal_sub]
  have hftc := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun t _ => kinkAnti_hasDerivAt hz0 (Real.log n) t) hint (kinkAnti_tendsto hz (Real.log n))
  rw [hrestr, hcongr, hftc]
  simp only [sub_self, zero_div, zero_sub]
  have hsq : (Complex.I * z) ^ 2 = -(z ^ 2) := by
    rw [mul_pow, Complex.I_sq]
    ring
  rw [hsq, div_neg, neg_neg]
  ring

/-- **The kink's transform is the Dirichlet-series term**:
`Λ(n) n^{−½} e^{iz log n} = Λ(n) n^{−s}`, `s = ½ − iz`. -/
theorem windingWeight_mul_exp_log (z : ℂ) {n : ℕ} (hn : 0 < n) :
    windingWeight n * Complex.exp (Complex.I * z * Real.log n)
      = LSeries.term (fun n => ((Λ n : ℝ) : ℂ)) (1 / 2 - Complex.I * z) n := by
  have hn0 : n ≠ 0 := by omega
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn0
  have hpow : (n : ℂ) ^ (1 / 2 - Complex.I * z) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]
    rintro ⟨h, _⟩
    exact hnC h
  have hexp : Complex.exp (Complex.I * z * Real.log n) = (n : ℂ) ^ (Complex.I * z) := by
    rw [Complex.cpow_def_of_ne_zero hnC, ← Complex.natCast_log]
    congr 1
    ring
  rw [LSeries.term_of_ne_zero hn0, eq_div_iff hpow]
  unfold windingWeight
  rw [hexp, mul_assoc, mul_assoc, ← Complex.cpow_add _ _ hnC, ← Complex.cpow_add _ _ hnC]
  have h0 : (((-(1 / 2 : ℝ)) : ℝ) : ℂ) + (Complex.I * z + (1 / 2 - Complex.I * z)) = 0 := by
    push_cast
    ring
  rw [h0, Complex.cpow_zero, mul_one]

/-- One ramp term's transform is `−z⁻²` times the Dirichlet-series term. -/
theorem rampTerm_laplace {z : ℂ} (hz : 0 < z.im) (n : ℕ) :
    ∫ t in Set.Ioi (0 : ℝ), rampTerm t n * Complex.exp (Complex.I * z * t)
      = -(1 / z ^ 2) * LSeries.term (fun n => ((Λ n : ℝ) : ℂ)) (1 / 2 - Complex.I * z) n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [rampTerm, windingWeight]
  · have hfun : (fun t : ℝ => rampTerm t n * Complex.exp (Complex.I * z * t))
        = fun t : ℝ => windingWeight n * ((kink n t : ℂ) * Complex.exp (Complex.I * z * t)) := by
      funext t
      unfold rampTerm
      ring
    rw [hfun, integral_const_mul, kink_laplace hz hn, ← windingWeight_mul_exp_log z hn]
    ring

/-- Each ramp integrand is integrable on the half-line. -/
theorem rampTerm_mul_exp_integrable {z : ℂ} (hz : 0 < z.im) (n : ℕ) :
    IntegrableOn (fun t : ℝ => rampTerm t n * Complex.exp (Complex.I * z * t))
      (Set.Ioi 0) volume := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [rampTerm, windingWeight]
  · have hfun : (fun t : ℝ => rampTerm t n * Complex.exp (Complex.I * z * t))
        = fun t : ℝ => windingWeight n * ((kink n t : ℂ) * Complex.exp (Complex.I * z * t)) := by
      funext t
      unfold rampTerm
      ring
    rw [hfun]
    exact (kink_mul_exp_integrable hz hn).const_mul _

/-! ## The norm integrals, exactly -/

/-- The real kink integral: `∫₀^∞ (t − log n)₊ e^{−bt} dt = b⁻² n^{−b}` (`b > 0`). -/
theorem kink_integral_real {b : ℝ} (hb : 0 < b) {n : ℕ} (hn : 0 < n) :
    ∫ t in Set.Ioi (0 : ℝ), kink n t * Real.exp (-b * t) = (1 / b ^ 2) * (n : ℝ) ^ (-b) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hzim : 0 < (Complex.I * (b : ℂ)).im := by simp [hb]
  have h := kink_laplace hzim hn
  have hexp : ∀ t : ℝ, Complex.exp (Complex.I * (Complex.I * b) * t)
      = ((Real.exp (-b * t) : ℝ) : ℂ) := by
    intro t
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    linear_combination ((b : ℂ) * (t : ℂ)) * Complex.I_mul_I
  simp_rw [hexp] at h
  have hlhs : (∫ t in Set.Ioi (0 : ℝ), ((kink n t : ℝ) : ℂ) * ((Real.exp (-b * t) : ℝ) : ℂ))
      = ((∫ t in Set.Ioi (0 : ℝ), kink n t * Real.exp (-b * t) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    simp_rw [Complex.ofReal_mul]
  have he : Real.exp (-b * Real.log n) = (n : ℝ) ^ (-b) := by
    rw [Real.rpow_def_of_pos hnpos]
    congr 1
    ring
  have hrhs : -(1 / (Complex.I * b) ^ 2) * ((Real.exp (-b * Real.log n) : ℝ) : ℂ)
      = (((1 / b ^ 2) * (n : ℝ) ^ (-b) : ℝ) : ℂ) := by
    rw [he, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_pow,
      mul_pow, Complex.I_sq]
    ring
  rw [hlhs, hrhs] at h
  exact Complex.ofReal_injective h

/-- **The norm integral of one ramp term, exactly**: `(Im z)⁻² Λ(n) n^{−(½ + Im z)}`. -/
theorem rampTerm_integral_norm {z : ℂ} (hz : 0 < z.im) {n : ℕ} (hn : 0 < n) :
    ∫ t in Set.Ioi (0 : ℝ), ‖rampTerm t n * Complex.exp (Complex.I * z * t)‖
      = (1 / z.im ^ 2) * ((Λ n : ℝ) * (n : ℝ) ^ (-(1 / 2 + z.im))) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hnorm : ∀ t : ℝ, ‖rampTerm t n * Complex.exp (Complex.I * z * t)‖
      = ((Λ n : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ))) * (kink n t * Real.exp (-z.im * t)) := by
    intro t
    unfold rampTerm windingWeight
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg, abs_of_nonneg (kink_nonneg n t),
      norm_exp_I_mul_ofReal, Complex.norm_natCast_cpow_of_pos hn, Complex.ofReal_re]
    ring
  simp_rw [hnorm]
  rw [integral_const_mul, kink_integral_real hz hn]
  have hsplit : (n : ℝ) ^ (-(1 / 2 + z.im)) = (n : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-z.im) := by
    rw [← Real.rpow_add hnpos]
    congr 1
    ring
  rw [hsplit]
  ring

/-- The norm integrals are summable: they are the von Mangoldt Dirichlet series at the real
abscissa `½ + Im z > 1`. -/
theorem rampTerm_integral_norm_summable {z : ℂ} (hz : 1 / 2 < z.im) :
    Summable (fun n : ℕ =>
      ∫ t in Set.Ioi (0 : ℝ), ‖rampTerm t n * Complex.exp (Complex.I * z * t)‖) := by
  have hb : 0 < z.im := by linarith
  have hs : 1 < (((1 / 2 + z.im : ℝ) : ℝ) : ℂ).re := by
    rw [Complex.ofReal_re]
    linarith
  have hsum := (LSeriesSummable_vonMangoldt hs).norm
  have hmaj : Summable (fun n : ℕ => (1 / z.im ^ 2)
      * ‖LSeries.term (fun n => ((Λ n : ℝ) : ℂ)) (((1 / 2 + z.im : ℝ) : ℝ) : ℂ) n‖) :=
    hsum.mul_left _
  refine hmaj.of_nonneg_of_le (fun n => integral_nonneg (fun _ => norm_nonneg _)) (fun n => ?_)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [rampTerm, windingWeight]
  · have hn0 : n ≠ 0 := by omega
    rw [rampTerm_integral_norm hb hn, LSeries.norm_term_eq, if_neg hn0, Complex.ofReal_re,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg,
      Real.rpow_neg (Nat.cast_nonneg n)]
    exact le_of_eq (by ring)

/-! ## The transform of the winding ramp -/

/-- **The winding ramp's transform is the von Mangoldt Dirichlet series** (Suzuki Thm 1.1(2),
field 2 of 3): for `Im z > ½` and `s = ½ − iz`,
`∫₀^∞ R(t) e^{izt} dt = −z⁻² · Σ_n Λ(n) n^{−s}`. -/
theorem rampProfile_laplace {z : ℂ} (hz : 1 / 2 < z.im) :
    ∫ t in Set.Ioi (0 : ℝ), rampProfile t * Complex.exp (Complex.I * z * t)
      = -(1 / z ^ 2) * LSeries (fun n => ((Λ n : ℝ) : ℂ)) (1 / 2 - Complex.I * z) := by
  have hb : 0 < z.im := by linarith
  have hpt : ∀ t : ℝ, rampProfile t * Complex.exp (Complex.I * z * t)
      = ∑' n : ℕ, rampTerm t n * Complex.exp (Complex.I * z * t) := by
    intro t
    unfold rampProfile
    rw [tsum_mul_right]
  simp_rw [hpt]
  have hF := hasSum_integral_of_summable_integral_norm
    (fun n => rampTerm_mul_exp_integrable hb n) (rampTerm_integral_norm_summable hz)
  rw [← hF.tsum_eq]
  simp_rw [rampTerm_laplace hb]
  rw [tsum_mul_left]
  rfl

end CriticalLinePhasor.HilbertPolya

#print axioms CriticalLinePhasor.HilbertPolya.kink_laplace
#print axioms CriticalLinePhasor.HilbertPolya.windingWeight_mul_exp_log
#print axioms CriticalLinePhasor.HilbertPolya.rampTerm_integral_norm
#print axioms CriticalLinePhasor.HilbertPolya.rampProfile_laplace
