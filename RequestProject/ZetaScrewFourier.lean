import RequestProject.ZetaScrewHelix
import RequestProject.SeatingFloorOdd
import RequestProject.DVPCarrierContinuation

/-!
# The helix profile's Fourier transform is the completed log-derivative (Track E)

Suzuki (arXiv:2206.03682, Thm 1.1(1)): `∫₀^∞ Ψ(t) e^{izt} dt = −z^{−2} (ξ′/ξ)(½ − iz)` for
`Im z > ½`.  Here it is derived from the house's compiled two-point resolvent trace
(`hilbertPolya_resolvent_trace`), termwise Laplace integrals, and Fubini:

* `zeta_half_ne_zero`, `half_not_mem_nontrivialZeros` — **the centre is not a zero**: the
  ordered carrier series at `½` is a sum of positive pairs
  `(2k+1)^{−½} − (2k+2)^{−½} > 0`, so `etaLim ½ ≠ 0` and `ζ(½) ≠ 0` by the compiled
  `etaLim_eq_zeta`.  (Needed so that `0` is an admissible resolvent point.)
* `xiLogDeriv_half` — `ξ′/ξ(½) = 0`, from the compiled oddness `xiLogDeriv_odd`.
* `screwTerm_laplace` — the Laplace transform of one screw term is
  `(i/z²)·m_ρ·[(t_ρ − 0)⁻¹ − (t_ρ + z)⁻¹]`: the two-point resolvent summand at `(−z, 0)`.
* `zetaScrew_fourier` — **`∫₀^∞ Ψ(t) e^{izt} dt = −z^{−2}·logDeriv ξ (½ − iz)`** for
  `Im z > ½`.  The helix profile is the time-domain of the resolvent trace; the constant
  is killed by the compiled two-point differencing, with `ξ′/ξ(½) = 0` as the second point.

With `seatMass_eta_form` (ordered readout + ends + Archimedean clock) this ties the
zero-side helix to the fiber's arithmetic readout at the level of exact identities.
No `sorry`, no `axiom`.
-/

open Complex Filter Topology MeasureTheory

noncomputable section

namespace CriticalLinePhasor.HilbertPolya

open CriticalLinePhasor.StBridge CriticalLinePhasor.DVP

/-! ## The centre is not a zero -/

/-- Each paired η term at `s = ½` is a real number. -/
theorem pairTerm_half_eq (k : ℕ) :
    pairTerm (1 / 2 : ℂ) k
      = ((((2 * k + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))
          - ((2 * k + 2 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
  rw [pairTerm_eq]
  have h1 : (((2 * k + 1 : ℕ) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ))
      = ((((2 * k + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow (Nat.cast_nonneg _)]
    push_cast
    ring_nf
  have h2 : (((2 * k + 2 : ℕ) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ))
      = ((((2 * k + 2 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow (Nat.cast_nonneg _)]
    push_cast
    ring_nf
  rw [h1, h2]
  push_cast
  ring

/-- Each paired η term at `s = ½` is positive. -/
theorem pairTerm_half_re_pos (k : ℕ) : 0 < (pairTerm (1 / 2 : ℂ) k).re := by
  rw [pairTerm_half_eq, Complex.ofReal_re]
  have ha : (0 : ℝ) < ((2 * k + 1 : ℕ) : ℝ) := by positivity
  have hab : ((2 * k + 1 : ℕ) : ℝ) < ((2 * k + 2 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 2 * k + 1 < 2 * k + 2)
  have := Real.rpow_lt_rpow_of_neg ha hab (by norm_num : (-(1 / 2 : ℝ)) < 0)
  linarith

/-- The ordered carrier series at the centre has positive real part. -/
theorem etaLim_half_re_pos : 0 < (etaLim (1 / 2 : ℂ)).re := by
  have hsum : Summable (pairTerm (1 / 2 : ℂ)) := by
    have h := paired_bank_summable (s := (1 / 2 : ℂ)) (by norm_num)
    exact h.congr (fun k => (pairTerm_eq _ k).symm)
  unfold etaLim
  rw [Complex.re_tsum hsum]
  exact Summable.tsum_pos (Complex.hasSum_re hsum.hasSum).summable
    (fun k => (pairTerm_half_re_pos k).le) 0 (pairTerm_half_re_pos 0)

theorem etaLim_half_ne_zero : etaLim (1 / 2 : ℂ) ≠ 0 := by
  intro h
  have := etaLim_half_re_pos
  rw [h, Complex.zero_re] at this
  exact lt_irrefl _ this

/-- The η-factor at the centre is `1 − √2 ≠ 0`. -/
theorem etaFactor_half_ne_zero : (1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - (1 / 2 : ℂ)) ≠ 0 := by
  have h : (2 : ℂ) ^ ((1 : ℂ) - (1 / 2 : ℂ)) = (((2 : ℝ) ^ ((1 : ℝ) / 2) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow (by norm_num : (0 : ℝ) ≤ 2)]
    push_cast
    norm_num
  rw [h]
  intro hz
  have h1 : (2 : ℝ) ^ ((1 : ℝ) / 2) = 1 := by
    have := congrArg Complex.re hz
    simp at this
    linarith
  have h2 : (1 : ℝ) < (2 : ℝ) ^ ((1 : ℝ) / 2) := by
    rw [Real.one_lt_rpow_iff (by norm_num)]
    left
    constructor <;> norm_num
  linarith

/-- **The centre is not a zero of ζ.** -/
theorem zeta_half_ne_zero : riemannZeta (1 / 2 : ℂ) ≠ 0 := by
  intro hz
  have h := etaLim_eq_zeta (s := (1 / 2 : ℂ)) (by norm_num) (by norm_num)
  rw [hz, mul_zero] at h
  exact etaLim_half_ne_zero h

theorem half_not_mem_nontrivialZeros : (1 / 2 : ℂ) ∉ ZD.NontrivialZeros :=
  fun h => zeta_half_ne_zero h.2.2

/-- The spectral coordinate of a nontrivial zero is nonzero. -/
theorem spectralCoord_ne_zero_of_mem {ρ : ℂ} (hρ : ρ ∈ ZD.NontrivialZeros) :
    spectralCoord ρ ≠ 0 := by
  intro h
  unfold spectralCoord at h
  have h1 : ρ - 1 / 2 = 0 := by
    rcases mul_eq_zero.mp h with h0 | h0
    · exact absurd h0 (neg_ne_zero.mpr Complex.I_ne_zero)
    · exact h0
  have : ρ = 1 / 2 := sub_eq_zero.mp h1
  exact half_not_mem_nontrivialZeros (this ▸ hρ)

/-! ## The completed log-derivative vanishes at the centre -/

theorem xiLogDeriv_half : logDeriv ZD.riemannXi (1 / 2) = 0 := by
  have h := CriticalLinePhasor.SeatingLedger.xiLogDeriv_odd (1 / 2 : ℂ)
  rw [show (1 : ℂ) - 1 / 2 = 1 / 2 by norm_num] at h
  linear_combination h / 2

/-! ## Termwise Laplace transform of the screw term -/

/-- The integrand `screwTerm t ρ · e^{izt}` as a difference of two exponentials in `t`. -/
theorem screwTerm_mul_exp_eq (z : ℂ) (ρ : Zeros) (t : ℝ) :
    screwTerm t ρ * Complex.exp (Complex.I * z * t)
      = ((ZD.xiOrderNat ρ.val : ℂ) / (spectralCoord ρ.val) ^ 2)
          * (Complex.exp ((Complex.I * z) * t)
            - Complex.exp ((Complex.I * (z + spectralCoord ρ.val)) * t)) := by
  unfold screwTerm
  have hE : Complex.exp (Complex.I * spectralCoord ρ.val * t) * Complex.exp (Complex.I * z * t)
      = Complex.exp ((Complex.I * (z + spectralCoord ρ.val)) * t) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [← hE]
  ring

/-- Re-part of the exponent `i·w`: `−Im w`. -/
theorem I_mul_re_neg (w : ℂ) : (Complex.I * w).re = -w.im := by
  simp [Complex.mul_re]

/-- **Laplace transform of one screw term** (`Im z > ½`): the two-point resolvent summand at
`(−z, 0)`, scaled by `i/z²`. -/
theorem screwTerm_laplace {z : ℂ} (hz : 1 / 2 < z.im) (ρ : Zeros) :
    ∫ t in Set.Ioi (0 : ℝ), screwTerm t ρ * Complex.exp (Complex.I * z * t)
      = (Complex.I / z ^ 2) * ((ZD.xiOrderNat ρ.val : ℂ)
          * ((spectralCoord ρ.val - 0)⁻¹ - (spectralCoord ρ.val - (-z))⁻¹)) := by
  have hτ0 : spectralCoord ρ.val ≠ 0 := spectralCoord_ne_zero_of_mem ρ.2
  have hτim := abs_lt.mp (spectralCoord_im_abs_lt_half ρ.2)
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, Complex.zero_im] at hz
    linarith
  have hzτ : z + spectralCoord ρ.val ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    rw [Complex.add_im, Complex.zero_im] at this
    linarith
  have ha₁ : (Complex.I * z).re < 0 := by
    rw [I_mul_re_neg]
    linarith
  have ha₂ : (Complex.I * (z + spectralCoord ρ.val)).re < 0 := by
    rw [I_mul_re_neg, Complex.add_im]
    linarith
  have hfun : (fun t : ℝ => screwTerm t ρ * Complex.exp (Complex.I * z * t))
      = fun t : ℝ => ((ZD.xiOrderNat ρ.val : ℂ) / (spectralCoord ρ.val) ^ 2)
          * (Complex.exp ((Complex.I * z) * t)
            - Complex.exp ((Complex.I * (z + spectralCoord ρ.val)) * t)) := by
    funext t
    exact screwTerm_mul_exp_eq z ρ t
  rw [hfun, integral_const_mul,
    integral_sub (integrableOn_exp_mul_complex_Ioi ha₁ 0)
      (integrableOn_exp_mul_complex_Ioi ha₂ 0),
    integral_exp_mul_complex_Ioi ha₁ 0, integral_exp_mul_complex_Ioi ha₂ 0]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, sub_zero, sub_neg_eq_add]
  have hτz : spectralCoord ρ.val + z ≠ 0 := by rw [add_comm]; exact hzτ
  have e1 : (Complex.I * z)⁻¹ = -Complex.I * z⁻¹ := by rw [mul_inv, Complex.inv_I]
  have e2 : (Complex.I * (z + spectralCoord ρ.val))⁻¹
      = -Complex.I * (z + spectralCoord ρ.val)⁻¹ := by rw [mul_inv, Complex.inv_I]
  simp only [div_eq_mul_inv, e1, e2]
  field_simp
  ring

/-! ## Fubini: the helix profile's Fourier transform -/

/-- `∫₀^∞ e^{−c t} dt = 1/c` for `c > 0`, via the complex exponential integral. -/
theorem integral_exp_neg_mul_Ioi_zero {c : ℝ} (hc : 0 < c) :
    ∫ t in Set.Ioi (0 : ℝ), Real.exp (-c * t) = 1 / c := by
  have hre : (((-c : ℝ) : ℂ)).re < 0 := by
    rw [Complex.ofReal_re]
    linarith
  have h := integral_exp_mul_complex_Ioi hre 0
  have hcast : ∀ t : ℝ, Complex.exp (((-c : ℝ) : ℂ) * (t : ℂ)) = ((Real.exp (-c * t) : ℝ) : ℂ) := by
    intro t
    rw [← Complex.ofReal_mul, Complex.ofReal_exp]
  simp_rw [hcast] at h
  rw [integral_complex_ofReal] at h
  have h' : ((∫ t in Set.Ioi (0 : ℝ), Real.exp (-c * t) : ℝ) : ℂ) = ((1 / c : ℝ) : ℂ) := by
    rw [h]
    push_cast
    simp
  exact_mod_cast h'

/-- The real exponential `e^{−c t}` is integrable on the half-line for `c > 0`. -/
theorem integrableOn_exp_neg_mul_Ioi_zero {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => Real.exp (-c * t)) (Set.Ioi 0) volume := by
  have hre : (((-c : ℝ) : ℂ)).re < 0 := by
    rw [Complex.ofReal_re]
    linarith
  have h : IntegrableOn (fun t : ℝ => ‖Complex.exp (((-c : ℝ) : ℂ) * (t : ℂ))‖) (Set.Ioi 0) volume :=
    (integrableOn_exp_mul_complex_Ioi hre 0).norm
  refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
  show ‖Complex.exp (((-c : ℝ) : ℂ) * (t : ℂ))‖ = Real.exp (-c * t)
  rw [Complex.norm_exp, ← Complex.ofReal_mul, Complex.ofReal_re]

/-- The norm bound on the integrand for `t ≥ 0`. -/
theorem screwTerm_mul_exp_norm_le {z : ℂ} (_hz : 1 / 2 < z.im) (ρ : Zeros) {t : ℝ} (ht : 0 ≤ t) :
    ‖screwTerm t ρ * Complex.exp (Complex.I * z * t)‖
      ≤ ((ZD.xiOrderNat ρ.val : ℝ) / ‖spectralCoord ρ.val‖ ^ 2)
          * (Real.exp (-z.im * t) + Real.exp (-(z.im - 1 / 2) * t)) := by
  rw [screwTerm_mul_exp_eq, norm_mul, norm_div, Complex.norm_natCast, norm_pow]
  have hτim := abs_lt.mp (spectralCoord_im_abs_lt_half ρ.2)
  have hE1 : ‖Complex.exp ((Complex.I * z) * t)‖ = Real.exp (-z.im * t) := by
    rw [Complex.norm_exp]
    congr 1
    simp [Complex.mul_re, Complex.mul_im]
  have hE2 : ‖Complex.exp ((Complex.I * (z + spectralCoord ρ.val)) * t)‖
      ≤ Real.exp (-(z.im - 1 / 2) * t) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have hre : ((Complex.I * (z + spectralCoord ρ.val)) * (t : ℂ)).re
        = -(z.im + (spectralCoord ρ.val).im) * t := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [hre]
    nlinarith
  have hsub : ‖Complex.exp ((Complex.I * z) * t)
      - Complex.exp ((Complex.I * (z + spectralCoord ρ.val)) * t)‖
      ≤ Real.exp (-z.im * t) + Real.exp (-(z.im - 1 / 2) * t) := by
    calc ‖Complex.exp ((Complex.I * z) * t)
          - Complex.exp ((Complex.I * (z + spectralCoord ρ.val)) * t)‖
        ≤ ‖Complex.exp ((Complex.I * z) * t)‖
          + ‖Complex.exp ((Complex.I * (z + spectralCoord ρ.val)) * t)‖ := norm_sub_le _ _
      _ ≤ Real.exp (-z.im * t) + Real.exp (-(z.im - 1 / 2) * t) := by
          rw [hE1]
          linarith
  exact mul_le_mul_of_nonneg_left hsub (by positivity)

/-- Each screw-term integrand is integrable on the half-line. -/
theorem screwTerm_mul_exp_integrable {z : ℂ} (hz : 1 / 2 < z.im) (ρ : Zeros) :
    IntegrableOn (fun t : ℝ => screwTerm t ρ * Complex.exp (Complex.I * z * t))
      (Set.Ioi 0) volume := by
  have hτim := abs_lt.mp (spectralCoord_im_abs_lt_half ρ.2)
  have ha₁ : (Complex.I * z).re < 0 := by
    rw [I_mul_re_neg]
    linarith
  have ha₂ : (Complex.I * (z + spectralCoord ρ.val)).re < 0 := by
    rw [I_mul_re_neg, Complex.add_im]
    linarith
  have hfun : (fun t : ℝ => screwTerm t ρ * Complex.exp (Complex.I * z * t))
      = fun t : ℝ => ((ZD.xiOrderNat ρ.val : ℂ) / (spectralCoord ρ.val) ^ 2)
          * (Complex.exp ((Complex.I * z) * t)
            - Complex.exp ((Complex.I * (z + spectralCoord ρ.val)) * t)) := by
    funext t
    exact screwTerm_mul_exp_eq z ρ t
  rw [hfun]
  exact ((integrableOn_exp_mul_complex_Ioi ha₁ 0).sub
    (integrableOn_exp_mul_complex_Ioi ha₂ 0)).const_mul _

/-- The integrated norms are summable over the zeros (counting majorant). -/
theorem screwTerm_integral_norm_summable {z : ℂ} (hz : 1 / 2 < z.im) :
    Summable (fun ρ : Zeros =>
      ∫ t in Set.Ioi (0 : ℝ), ‖screwTerm t ρ * Complex.exp (Complex.I * z * t)‖) := by
  have hb : 0 < z.im := by linarith
  have hb' : 0 < z.im - 1 / 2 := by linarith
  set K : ℝ := 1 / z.im + 1 / (z.im - 1 / 2) with hK
  have hK0 : 0 ≤ K := by positivity
  have hg : Summable (fun ρ : Zeros =>
      (4 * K) * ((ZD.xiOrderNat ρ.val : ℝ) / ‖ρ.val‖ ^ 2)) :=
    (ZD.summable_xiOrderNat_div_norm_sq_nontrivialZeros).mul_left _
  apply Summable.of_norm_bounded_eventually hg
  filter_upwards [eventually_cofinite_norm_ge 1] with ρ hbig
  have hsc := spectralCoord_norm_ge hbig
  have hsc0 : 0 < ‖spectralCoord ρ.val‖ := by linarith
  have hpos : 0 < ‖ρ.val‖ := by linarith
  have hm : (0 : ℝ) ≤ (ZD.xiOrderNat ρ.val : ℝ) := Nat.cast_nonneg _
  have hI1 := integrableOn_exp_neg_mul_Ioi_zero hb
  have hI2 := integrableOn_exp_neg_mul_Ioi_zero hb'
  have hFint := (screwTerm_mul_exp_integrable hz ρ).norm
  have hle : ∀ t ∈ Set.Ioi (0 : ℝ),
      ‖screwTerm t ρ * Complex.exp (Complex.I * z * t)‖
        ≤ ((ZD.xiOrderNat ρ.val : ℝ) / ‖spectralCoord ρ.val‖ ^ 2)
            * (Real.exp (-z.im * t) + Real.exp (-(z.im - 1 / 2) * t)) :=
    fun t ht => screwTerm_mul_exp_norm_le hz ρ (le_of_lt ht)
  have hbound : ∫ t in Set.Ioi (0 : ℝ), ‖screwTerm t ρ * Complex.exp (Complex.I * z * t)‖
      ≤ ((ZD.xiOrderNat ρ.val : ℝ) / ‖spectralCoord ρ.val‖ ^ 2) * K := by
    calc ∫ t in Set.Ioi (0 : ℝ), ‖screwTerm t ρ * Complex.exp (Complex.I * z * t)‖
        ≤ ∫ t in Set.Ioi (0 : ℝ), ((ZD.xiOrderNat ρ.val : ℝ) / ‖spectralCoord ρ.val‖ ^ 2)
            * (Real.exp (-z.im * t) + Real.exp (-(z.im - 1 / 2) * t)) :=
          setIntegral_mono_on hFint ((hI1.add hI2).const_mul _) measurableSet_Ioi hle
      _ = ((ZD.xiOrderNat ρ.val : ℝ) / ‖spectralCoord ρ.val‖ ^ 2)
            * ((∫ t in Set.Ioi (0 : ℝ), Real.exp (-z.im * t))
              + ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(z.im - 1 / 2) * t)) := by
          rw [integral_const_mul, integral_add hI1 hI2]
      _ = ((ZD.xiOrderNat ρ.val : ℝ) / ‖spectralCoord ρ.val‖ ^ 2) * K := by
          rw [integral_exp_neg_mul_Ioi_zero hb, integral_exp_neg_mul_Ioi_zero hb']
  have hnonneg : 0 ≤ ∫ t in Set.Ioi (0 : ℝ), ‖screwTerm t ρ * Complex.exp (Complex.I * z * t)‖ :=
    integral_nonneg (fun _ => norm_nonneg _)
  have h4 : ‖ρ.val‖ ^ 2 / 4 ≤ ‖spectralCoord ρ.val‖ ^ 2 := by
    nlinarith [hsc, norm_nonneg ρ.val]
  have hratio : (ZD.xiOrderNat ρ.val : ℝ) / ‖spectralCoord ρ.val‖ ^ 2
      ≤ 4 * ((ZD.xiOrderNat ρ.val : ℝ) / ‖ρ.val‖ ^ 2) := by
    rw [show 4 * ((ZD.xiOrderNat ρ.val : ℝ) / ‖ρ.val‖ ^ 2)
        = (ZD.xiOrderNat ρ.val : ℝ) / (‖ρ.val‖ ^ 2 / 4) by field_simp]
    exact div_le_div_of_nonneg_left hm (by positivity) h4
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  calc ∫ t in Set.Ioi (0 : ℝ), ‖screwTerm t ρ * Complex.exp (Complex.I * z * t)‖
      ≤ ((ZD.xiOrderNat ρ.val : ℝ) / ‖spectralCoord ρ.val‖ ^ 2) * K := hbound
    _ ≤ (4 * ((ZD.xiOrderNat ρ.val : ℝ) / ‖ρ.val‖ ^ 2)) * K :=
        mul_le_mul_of_nonneg_right hratio hK0
    _ = (4 * K) * ((ZD.xiOrderNat ρ.val : ℝ) / ‖ρ.val‖ ^ 2) := by ring

/-- **The Fourier transform of the helix profile is the completed log-derivative**
(Suzuki Thm 1.1(1), from the compiled two-point resolvent trace): for `Im z > ½`,
`∫₀^∞ Ψ(t) e^{izt} dt = −z^{−2}·(ξ′/ξ)(½ − iz)`. -/
theorem zetaScrew_fourier {z : ℂ} (hz : 1 / 2 < z.im) :
    ∫ t in Set.Ioi (0 : ℝ), zetaScrew t * Complex.exp (Complex.I * z * t)
      = -(1 / z ^ 2) * logDeriv ZD.riemannXi (1 / 2 - Complex.I * z) := by
  have hpt : ∀ t : ℝ, zetaScrew t * Complex.exp (Complex.I * z * t)
      = ∑' ρ : Zeros, screwTerm t ρ * Complex.exp (Complex.I * z * t) := by
    intro t
    unfold zetaScrew
    rw [tsum_mul_right]
  simp_rw [hpt]
  have hF := hasSum_integral_of_summable_integral_norm
    (fun ρ => screwTerm_mul_exp_integrable hz ρ) (screwTerm_integral_norm_summable hz)
  rw [← hF.tsum_eq]
  simp_rw [screwTerm_laplace hz]
  rw [tsum_mul_left]
  have hw : (1 / 2 + Complex.I * (-z)) ∉ ZD.NontrivialZeros := by
    intro h
    have h1 : (1 / 2 + Complex.I * (-z)).re < 1 := h.2.1
    have h2 : (1 / 2 + Complex.I * (-z)).re = 1 / 2 + z.im := by
      simp [Complex.mul_re]
    linarith
  have hw₀ : (1 / 2 + Complex.I * (0 : ℂ)) ∉ ZD.NontrivialZeros := by
    rw [mul_zero, add_zero]
    exact half_not_mem_nontrivialZeros
  have htrace := hilbertPolya_resolvent_trace hw hw₀
  have hneg : ∑' ρ : Zeros, (ZD.xiOrderNat ρ.val : ℂ)
        * ((spectralCoord ρ.val - 0)⁻¹ - (spectralCoord ρ.val - (-z))⁻¹)
      = -∑' ρ : Zeros, (ZD.xiOrderNat ρ.val : ℂ)
        * ((spectralCoord ρ.val - (-z))⁻¹ - (spectralCoord ρ.val - 0)⁻¹) := by
    rw [← tsum_neg]
    exact tsum_congr (fun ρ => by ring)
  rw [hneg, htrace]
  have h0 : deriv ZD.riemannXi (1 / 2 + Complex.I * 0) / ZD.riemannXi (1 / 2 + Complex.I * 0) = 0 := by
    rw [mul_zero, add_zero, ← logDeriv_apply, xiLogDeriv_half]
  rw [h0, logDeriv_apply, show (1 / 2 : ℂ) + Complex.I * (-z) = 1 / 2 - Complex.I * z by ring]
  set D : ℂ := deriv ZD.riemannXi (1 / 2 - Complex.I * z) / ZD.riemannXi (1 / 2 - Complex.I * z)
  linear_combination (D / z ^ 2) * Complex.I_sq

end CriticalLinePhasor.HilbertPolya

#print axioms CriticalLinePhasor.HilbertPolya.zeta_half_ne_zero
#print axioms CriticalLinePhasor.HilbertPolya.half_not_mem_nontrivialZeros
#print axioms CriticalLinePhasor.HilbertPolya.xiLogDeriv_half
#print axioms CriticalLinePhasor.HilbertPolya.screwTerm_laplace
#print axioms CriticalLinePhasor.HilbertPolya.zetaScrew_fourier
