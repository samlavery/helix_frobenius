import RequestProject.HelixTwoEndedCancellation
import RequestProject.XiKernelThetaBridge

/-!
# The feet never vanish: the two-ended mass is positive at every cut and every height (ledger 1263)

The mass of the two-ended configuration is the magnitude of the two cancelling banks: `‖helix foot‖ + ‖anti-helix
foot‖`. The cancellation is about `0`; it is the resultant that vanishes. This file proves that the mass never
does, at every physical height `Z` and every signed cut height `hc`. It discharges the hypothesis `hm` of
`HelixTwoEndedCancellation.twoEndedEigenstate`.

**Mechanism: the zero mode dominates.** The bank is `θ(x) = Σ_n e^{-πn²x}`. Its zero mode is exactly `1`; the
remaining modes `g = θ - 1 ≥ 0` decrease with height (`bankSlope_nonpos`, from the compiled termwise derivative
`XiKernelBridge.hasDerivAt_thetaSum`). A foot is the helix end above the cut `c = e^{hc}`,
`E(c,s) = ∫_c^∞ x^{s-1} g(x) dx - c^s/s`, with `s = ¼ + i·log Z / 2` (the event's offset from the origin; `¼` is the
bank's half-density centre `k/2`). Integrating by parts along the helix gives

  `s·E(c,s) = -c^s·θ(c) - ∫_c^∞ x^s θ'(x) dx`.

The first term is the zero mode booked at the cut, of size `c^{¼}·θ(c)`. The second is at most
`∫ x^{¼}(-θ') = c^{¼}·g(c) + ¼∫ x^{-¾} g`. Hence (`foot_bound`)

  `‖s·E(c,s)‖ ≥ c^{¼} - ¼∫_c^∞ x^{-¾} g(x) dx ≥ c^{¼} - e^{-c}`   for `c ≥ 1`,

uniformly in the height. The bound `g(x) ≤ 4e^{-x}` (`bank_modes_le`) is Mathlib's `norm_jacobiTheta_sub_one_le`.
At every cut one of `c = e^{hc}` and `e^{-hc}` is `≥ 1`, so one of the two feet is nonzero:
* `helixFoot_ne_zero` (cut at or above the origin), `antiHelixFoot_ne_zero` (cut at or below the origin);
* `twoEnded_mass_pos`: **`0 < mass` for every `Z` and every `hc`.**
* `cancellationEigenstate`, `cancellation_post_state`: the post-cancellation eigenstate `(M, Z)`, with no
  hypothesis on `M`.

The integration by parts is done on finite stretches `[c, R]`, and the lower bound is passed to `R → ∞`, so no
decay estimate on `θ'` is needed.
-/

open Complex Set MeasureTheory Filter Topology
open scoped ComplexConjugate Interval

noncomputable section

namespace CriticalLinePhasor.HelixFootMass

open CriticalLinePhasor CriticalLinePhasor.GlobalHelix CriticalLinePhasor.HelixTwoEndedClosure
  CriticalLinePhasor.HelixTwoEndedNative CriticalLinePhasor.HelixOriginCentered
  CriticalLinePhasor.HelixTwoEndedCancellation CriticalLinePhasor.FocalFeet
  CriticalLinePhasor.XiKernelBridge CriticalLinePhasor.ThetaWronskianSuzukiGram

/-! ## The bank: zero mode, nonzero modes, slope -/

/-- The bank's slope in the encoded height `x = e^h`: the termwise derivative of the nonzero modes. -/
def bankSlope (x : ℝ) : ℝ := (∑' n : ℕ, xiThetaSeriesDeriv1 n (Real.log x / 2)) / x

theorem theta_eq_thetaSum {x : ℝ} (hx : 0 < x) :
    gaussianLatticeTheta x = 1 + 2 * thetaSum (Real.log x / 2) := by
  rw [thetaSum_eq, show 2 * (Real.log x / 2) = Real.log x by ring, Real.exp_log hx,
    gaussianLatticeTheta_eq_evenKernel hx]
  ring

theorem thetaSum_nonneg (u : ℝ) : 0 ≤ thetaSum u :=
  tsum_nonneg fun n => by simp only [xiThetaSeriesTerm]; positivity

/-- The zero mode is `1` and the other modes are nonnegative. -/
theorem one_le_theta {x : ℝ} (hx : 0 < x) : 1 ≤ gaussianLatticeTheta x := by
  rw [theta_eq_thetaSum hx]
  linarith [thetaSum_nonneg (Real.log x / 2)]

theorem hasDerivAt_theta {x : ℝ} (hx : 0 < x) : HasDerivAt gaussianLatticeTheta (bankSlope x) x := by
  have hlog : HasDerivAt (fun y => Real.log y / 2) (x⁻¹ / 2) x := (Real.hasDerivAt_log hx.ne').div_const 2
  have h := (((hasDerivAt_thetaSum (Real.log x / 2)).comp x hlog).const_mul 2).const_add 1
  have heq : gaussianLatticeTheta =ᶠ[𝓝 x] fun y => 1 + 2 * (thetaSum ∘ fun y => Real.log y / 2) y := by
    filter_upwards [lt_mem_nhds hx] with y hy
    simp only [Function.comp]
    exact theta_eq_thetaSum hy
  refine (h.congr_of_eventuallyEq heq).congr_deriv ?_
  unfold bankSlope
  ring

theorem bankSlope_nonpos {x : ℝ} (hx : 0 < x) : bankSlope x ≤ 0 := by
  unfold bankSlope
  apply div_nonpos_of_nonpos_of_nonneg _ hx.le
  apply tsum_nonpos
  intro n
  have hQ : 0 ≤ xiKernelQ n (Real.log x / 2) := by simp only [xiKernelQ]; positivity
  have := mul_nonneg hQ (Real.exp_pos (-xiKernelQ n (Real.log x / 2))).le
  simp only [xiThetaSeriesDeriv1]
  linarith

theorem continuousOn_bankSlope : ContinuousOn bankSlope (Ioi 0) := by
  intro x hx
  have hx0 : x ≠ 0 := (mem_Ioi.mp hx).ne'
  have hT : ContinuousAt (fun v => ∑' n : ℕ, xiThetaSeriesDeriv1 n v) (Real.log x / 2) :=
    (hasDerivAt_tsum_Deriv1 _).continuousAt
  have hl : ContinuousAt (fun y => Real.log y / 2) x := (Real.continuousAt_log hx0).div_const 2
  have : ContinuousAt bankSlope x :=
    (ContinuousAt.comp (f := fun y => Real.log y / 2) hT hl).div continuousAt_id hx0
  exact this.continuousWithinAt

/-- The nonzero modes above the origin: `g(x) ≤ 4 e^{-x}` for `x ≥ 1` (Mathlib's Jacobi theta bound). -/
theorem bank_modes_le {x : ℝ} (hx : 1 ≤ x) : gaussianLatticeTheta x - 1 ≤ 4 * Real.exp (-x) := by
  have hx0 : 0 < x := by linarith
  have hk : ((HurwitzZeta.evenKernel 0 x : ℝ) : ℂ) = jacobiTheta (I * x) := by
    have := HurwitzZeta.evenKernel_def 0 x
    simpa [jacobiTheta_eq_jacobiTheta₂] using this
  have him : (I * (x : ℂ)).im = x := by simp
  have hb := norm_jacobiTheta_sub_one_le (τ := I * (x : ℂ)) (by rw [him]; exact hx0)
  rw [him] at hb
  have hre : gaussianLatticeTheta x - 1 ≤ ‖jacobiTheta (I * x) - 1‖ := by
    rw [gaussianLatticeTheta_eq_evenKernel hx0, ← hk, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs]
    exact le_abs_self _
  have hpi := Real.pi_gt_three
  have he1 : Real.exp (-Real.pi * x) ≤ Real.exp (-x) := Real.exp_le_exp.mpr (by nlinarith)
  have he2 : Real.exp (-Real.pi * x) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by nlinarith)
  have hhalf := Real.exp_neg_one_lt_half
  have hpos : 0 < Real.exp (-Real.pi * x) := Real.exp_pos _
  calc gaussianLatticeTheta x - 1 ≤ 2 / (1 - Real.exp (-Real.pi * x)) * Real.exp (-Real.pi * x) := hre.trans hb
    _ ≤ 4 * Real.exp (-Real.pi * x) := by
        apply mul_le_mul_of_nonneg_right _ hpos.le
        rw [div_le_iff₀ (by linarith)]
        linarith
    _ ≤ 4 * Real.exp (-x) := by linarith

/-! ## Integration by parts along a finite stretch of the helix -/

theorem pos_of_mem {c R x : ℝ} (hc : 0 < c) (hcR : c ≤ R) (hx : x ∈ [[c, R]]) : 0 < x := by
  rw [uIcc_of_le hcR] at hx
  exact hc.trans_le hx.1

/-- Integration by parts against the bank on `[c, R]`, for every exponent `s`. -/
theorem byParts {c R : ℝ} (hc : 0 < c) (hcR : c ≤ R) (s : ℂ) :
    ∫ x in c..R, (x : ℂ) ^ s * (bankSlope x : ℂ) =
      (R : ℂ) ^ s * ((gaussianLatticeTheta R : ℂ) - 1) - (c : ℂ) ^ s * ((gaussianLatticeTheta c : ℂ) - 1) -
        s * ∫ x in c..R, (x : ℂ) ^ (s - 1) * ((gaussianLatticeTheta x : ℂ) - 1) := by
  have hu : ∀ x ∈ [[c, R]], HasDerivAt (fun y : ℝ => (y : ℂ) ^ s) (s * (x : ℂ) ^ (s - 1)) x := fun x hx =>
    (Complex.hasStrictDerivAt_cpow_const
      (Complex.ofReal_mem_slitPlane.mpr (pos_of_mem hc hcR hx))).hasDerivAt.comp_ofReal
  have hv : ∀ x ∈ [[c, R]], HasDerivAt (fun y : ℝ => (gaussianLatticeTheta y : ℂ) - 1) (bankSlope x : ℂ) x :=
    fun x hx => (hasDerivAt_theta (pos_of_mem hc hcR hx)).ofReal_comp.sub_const 1
  have hu' : IntervalIntegrable (fun x : ℝ => s * (x : ℂ) ^ (s - 1)) volume c R := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    exact (continuousAt_const.mul (Complex.continuousAt_ofReal_cpow_const _ _
      (Or.inr (pos_of_mem hc hcR hx).ne'))).continuousWithinAt
  have hv' : IntervalIntegrable (fun x : ℝ => (bankSlope x : ℂ)) volume c R := by
    apply ContinuousOn.intervalIntegrable
    exact continuous_ofReal.comp_continuousOn
      (continuousOn_bankSlope.mono fun x hx => pos_of_mem hc hcR hx)
  rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu' hv']
  simp_rw [mul_assoc]
  rw [intervalIntegral.integral_const_mul]

/-- The same integration by parts at the bank's centre exponent `¼`, in real form. -/
theorem byParts_centre {c R : ℝ} (hc : 0 < c) (hcR : c ≤ R) :
    ∫ x in c..R, x ^ (1 / 4 : ℝ) * bankSlope x =
      R ^ (1 / 4 : ℝ) * (gaussianLatticeTheta R - 1) - c ^ (1 / 4 : ℝ) * (gaussianLatticeTheta c - 1) -
        1 / 4 * ∫ x in c..R, x ^ (-(3 / 4) : ℝ) * (gaussianLatticeTheta x - 1) := by
  have hu : ∀ x ∈ [[c, R]], HasDerivAt (fun y : ℝ => y ^ (1 / 4 : ℝ)) (1 / 4 * x ^ (-(3 / 4) : ℝ)) x :=
    fun x hx => by
      have h := Real.hasDerivAt_rpow_const (p := (1 / 4 : ℝ)) (Or.inl (pos_of_mem hc hcR hx).ne')
      rwa [show (1 / 4 : ℝ) - 1 = -(3 / 4) by norm_num] at h
  have hv : ∀ x ∈ [[c, R]], HasDerivAt (fun y : ℝ => gaussianLatticeTheta y - 1) (bankSlope x) x :=
    fun x hx => (hasDerivAt_theta (pos_of_mem hc hcR hx)).sub_const 1
  have hu' : IntervalIntegrable (fun x : ℝ => 1 / 4 * x ^ (-(3 / 4) : ℝ)) volume c R := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    exact (continuousAt_const.mul
      (Real.continuousAt_rpow_const _ _ (Or.inl (pos_of_mem hc hcR hx).ne'))).continuousWithinAt
  have hv' : IntervalIntegrable bankSlope volume c R :=
    (continuousOn_bankSlope.mono fun x hx => pos_of_mem hc hcR hx).intervalIntegrable
  rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu' hv']
  simp_rw [mul_assoc]
  rw [intervalIntegral.integral_const_mul]

/-! ## The zero mode dominates -/

/-- **Finite-stretch bound.** On the event offset (`Re s = ¼`), the zero mode booked at the cut dominates. -/
theorem foot_bound_finite {c R : ℝ} (hc : 0 < c) (hcR : c ≤ R) {s : ℂ} (hs : s.re = 1 / 4) :
    c ^ (1 / 4 : ℝ) - 1 / 4 * ∫ x in c..R, x ^ (-(3 / 4) : ℝ) * (gaussianLatticeTheta x - 1) ≤
      ‖s * (∫ x in c..R, (x : ℂ) ^ (s - 1) * ((gaussianLatticeTheta x : ℂ) - 1)) - (c : ℂ) ^ s‖ := by
  have hR : 0 < R := hc.trans_le hcR
  have hA := byParts hc hcR s
  have hAr := byParts_centre hc hcR
  set A := ∫ x in c..R, (x : ℂ) ^ s * (bankSlope x : ℂ) with hAdef
  set J := ∫ x in c..R, (x : ℂ) ^ (s - 1) * ((gaussianLatticeTheta x : ℂ) - 1)
  -- `‖A‖ ≤ ∫ x^{¼}(-θ')`
  have hnormA : ‖A‖ ≤ -∫ x in c..R, x ^ (1 / 4 : ℝ) * bankSlope x := by
    calc ‖A‖ ≤ ∫ x in c..R, ‖(x : ℂ) ^ s * (bankSlope x : ℂ)‖ :=
          intervalIntegral.norm_integral_le_integral_norm hcR
      _ = ∫ x in c..R, -(x ^ (1 / 4 : ℝ) * bankSlope x) := by
          apply intervalIntegral.integral_congr
          intro x hx
          have hx0 := pos_of_mem hc hcR hx
          simp only
          rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0, hs, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonpos (bankSlope_nonpos hx0)]
          ring
      _ = -∫ x in c..R, x ^ (1 / 4 : ℝ) * bankSlope x := intervalIntegral.integral_neg
  have hθc := one_le_theta hc
  have hθR := one_le_theta hR
  have h1 : ‖(c : ℂ) ^ s * (gaussianLatticeTheta c : ℂ)‖ = c ^ (1 / 4 : ℝ) * gaussianLatticeTheta c := by
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hc, hs, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith)]
  have h2 : ‖(R : ℂ) ^ s * ((gaussianLatticeTheta R : ℂ) - 1)‖ =
      R ^ (1 / 4 : ℝ) * (gaussianLatticeTheta R - 1) := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hR, hs,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  have hkey : (c : ℂ) ^ s * (gaussianLatticeTheta c : ℂ) =
      (R : ℂ) ^ s * ((gaussianLatticeTheta R : ℂ) - 1) - A - (s * J - (c : ℂ) ^ s) := by
    rw [hA]
    ring
  have htri : ‖(c : ℂ) ^ s * (gaussianLatticeTheta c : ℂ)‖ ≤
      ‖(R : ℂ) ^ s * ((gaussianLatticeTheta R : ℂ) - 1)‖ + ‖A‖ + ‖s * J - (c : ℂ) ^ s‖ := by
    rw [hkey]
    exact (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
  rw [h1, h2] at htri
  linarith

/-- The nonzero-mode integral above a cut at or above the origin: `¼∫_c^R x^{-¾} g ≤ e^{-c}`. -/
theorem modes_integral_le {c R : ℝ} (hc : 1 ≤ c) (hcR : c ≤ R) :
    1 / 4 * ∫ x in c..R, x ^ (-(3 / 4) : ℝ) * (gaussianLatticeTheta x - 1) ≤ Real.exp (-c) := by
  have hc0 : 0 < c := by linarith
  have hint : IntervalIntegrable (fun x : ℝ => x ^ (-(3 / 4) : ℝ) * (gaussianLatticeTheta x - 1)) volume c R := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    have hx0 := pos_of_mem hc0 hcR hx
    exact ((Real.continuousAt_rpow_const _ _ (Or.inl hx0.ne')).continuousWithinAt).mul
      ((gaussianLatticeTheta_continuousOn.mono fun y hy => pos_of_mem hc0 hcR hy) x hx |>.sub
        continuousWithinAt_const)
  have hexp : IntervalIntegrable (fun x : ℝ => 4 * Real.exp (-x)) volume c R :=
    (by fun_prop : Continuous fun x : ℝ => 4 * Real.exp (-x)).intervalIntegrable _ _
  have hmono : ∫ x in c..R, x ^ (-(3 / 4) : ℝ) * (gaussianLatticeTheta x - 1) ≤
      ∫ x in c..R, 4 * Real.exp (-x) := by
    apply intervalIntegral.integral_mono_on hcR hint hexp
    intro x hx
    have hx1 : 1 ≤ x := hc.trans hx.1
    have hx0 : 0 < x := by linarith
    have hg0 : 0 ≤ gaussianLatticeTheta x - 1 := by linarith [one_le_theta hx0]
    have hp : x ^ (-(3 / 4) : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by norm_num)
    have hp0 : 0 ≤ x ^ (-(3 / 4) : ℝ) := Real.rpow_nonneg hx0.le _
    calc x ^ (-(3 / 4) : ℝ) * (gaussianLatticeTheta x - 1) ≤ 1 * (gaussianLatticeTheta x - 1) :=
          mul_le_mul_of_nonneg_right hp hg0
      _ ≤ 4 * Real.exp (-x) := by linarith [bank_modes_le hx1]
  have hcalc : ∫ x in c..R, 4 * Real.exp (-x) = 4 * (Real.exp (-c) - Real.exp (-R)) := by
    rw [intervalIntegral.integral_const_mul]
    congr 1
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x : ℝ => -Real.exp (-x))
      (f' := fun x : ℝ => Real.exp (-x)) (a := c) (b := R)
      (fun x _ => (((hasDerivAt_neg x).exp).neg).congr_deriv (by ring))
      ((by fun_prop : Continuous fun x : ℝ => Real.exp (-x)).intervalIntegrable _ _)
    rw [this]
    ring
  have hR := Real.exp_pos (-R)
  linarith

/-- **The zero mode dominates, at every height.** For a cut at or above the origin (`c ≥ 1` in the encoding) and
the event offset `Re s = ¼`: `‖s·E(c,s)‖ ≥ c^{¼} - e^{-c}`. -/
theorem foot_bound {c : ℝ} (hc : 1 ≤ c) {s : ℂ} (hs : s.re = 1 / 4) :
    c ^ (1 / 4 : ℝ) - Real.exp (-c) ≤ ‖s * helixEndAt nativePair c s‖ := by
  have hc0 : 0 < c := by linarith
  have hs0 : s ≠ 0 := fun h => by rw [h, Complex.zero_re] at hs; norm_num at hs
  have hE : s * helixEndAt nativePair c s = s * helixStrandAt nativePair c s - (c : ℂ) ^ s := by
    unfold helixEndAt
    have : nativePair.f₀ = 1 := rfl
    rw [this]
    field_simp
  have hlim0 := intervalIntegral_tendsto_integral_Ioi c (integrableOn_strand nativePair hc0 s) tendsto_id
  have hlim : Tendsto (fun R : ℝ => ∫ x in c..R, (x : ℂ) ^ (s - 1) * ((gaussianLatticeTheta x : ℂ) - 1))
      atTop (𝓝 (helixStrandAt nativePair c s)) := by
    refine hlim0.congr' ?_
    filter_upwards [eventually_ge_atTop c] with R hR
    apply intervalIntegral.integral_congr
    intro x hx
    beta_reduce
    have : nativePair.f x = (gaussianLatticeTheta x : ℂ) := helixBank_eq (pos_of_mem hc0 hR hx)
    rw [this]
    rfl
  have hlim2 := ((hlim.const_mul s).sub_const ((c : ℂ) ^ s)).norm
  rw [hE]
  apply ge_of_tendsto hlim2
  filter_upwards [eventually_ge_atTop c] with R hR
  have h1 := foot_bound_finite hc0 hR hs
  have h2 := modes_integral_le hc hR
  linarith

/-! ## The feet and the mass -/

theorem event_re (Z : ℝ) : ((nativePair.k : ℂ) / 2 + eventOffset Z).re = 1 / 4 := by
  rw [nativePair_k]
  simp [eventOffset]
  norm_num

theorem helixEndAt_ne_zero {c : ℝ} (hc : 1 ≤ c) (Z : ℝ) :
    helixEndAt nativePair c ((nativePair.k : ℂ) / 2 + eventOffset Z) ≠ 0 := by
  intro h
  have hb := foot_bound hc (event_re Z)
  rw [h, mul_zero, norm_zero] at hb
  have h1 : 1 ≤ c ^ (1 / 4 : ℝ) := Real.one_le_rpow hc (by norm_num)
  have h2 : Real.exp (-c) < 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  linarith

/-- With the cut at or above the origin, the helix foot is nonzero, at every height. -/
theorem helixFoot_ne_zero (Z : ℝ) {hc : ℝ} (h : 0 ≤ hc) : helixFoot Z hc ≠ 0 :=
  helixEndAt_ne_zero (Real.one_le_exp h) Z

/-- With the cut at or below the origin, the anti-helix foot is nonzero, at every height. -/
theorem antiHelixFoot_ne_zero (Z : ℝ) {hc : ℝ} (h : hc ≤ 0) : antiHelixFoot Z hc ≠ 0 := by
  unfold antiHelixFoot
  rw [map_ne_zero]
  exact helixEndAt_ne_zero (Real.one_le_exp (by linarith)) Z

theorem mass_eq (Z hc : ℝ) : (twoEndedConfig Z hc).mass = ‖helixFoot Z hc‖ + ‖antiHelixFoot Z hc‖ := by
  show ∑ k : Fin 2, ‖(![helixFoot Z hc, antiHelixFoot Z hc] : Fin 2 → ℂ) k‖ = _
  rw [Fin.sum_univ_two]
  rfl

/-- **The mass is positive at every cut and every height.** -/
theorem twoEnded_mass_pos (Z hc : ℝ) : 0 < (twoEndedConfig Z hc).mass := by
  rw [mass_eq]
  rcases le_total 0 hc with h | h
  · exact add_pos_of_pos_of_nonneg (norm_pos_iff.mpr (helixFoot_ne_zero Z h)) (norm_nonneg _)
  · exact add_pos_of_nonneg_of_pos (norm_nonneg _) (norm_pos_iff.mpr (antiHelixFoot_ne_zero Z h))

/-- **The post-cancellation eigenstate** `(M, Z)`, with `M > 0` proved. -/
def cancellationEigenstate (Z hc : ℝ) (hZ : 0 < Z) : FocalEigenstate :=
  twoEndedEigenstate Z hc hZ (twoEnded_mass_pos Z hc)

/-- **Cancellation → standing mode → eigenstate**, with no hypothesis on the mass. -/
theorem cancellation_post_state {Z hc : ℝ} (hZ : 0 < Z) (h : (twoEndedConfig Z hc).Cancels) :
    (twoEndedConfig Z hc).channels = ((cancellationEigenstate Z hc hZ).standing, Z) :=
  twoEnded_post_state hZ _ h

end CriticalLinePhasor.HelixFootMass

end

#print axioms CriticalLinePhasor.HelixFootMass.foot_bound
#print axioms CriticalLinePhasor.HelixFootMass.helixFoot_ne_zero
#print axioms CriticalLinePhasor.HelixFootMass.antiHelixFoot_ne_zero
#print axioms CriticalLinePhasor.HelixFootMass.twoEnded_mass_pos
#print axioms CriticalLinePhasor.HelixFootMass.cancellation_post_state
