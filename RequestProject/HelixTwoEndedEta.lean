import RequestProject.HelixTwoEndedNative

/-!
# The conductor (η) routing through the same native 3D involution (ledger 1255)

The η routing is an indexed Gaussian bank on the 3D helix: amplitudes `(2, -1, 0)` at index heights
`(4, 1, ¼)`, i.e. the full alternating bank `Σ_{n∈ℤ} (-1)^n e^{-πn²x} = 2θ(4x) - θ(x)` (constant mode `1`, the
zero mode `n = 0`). The compiled 3D reflection `indexedGaussian3D_globalHelixReflection` (global helix involution,
exact height shear, conjugated dual coefficients `a(dual⁻¹ i)·H(i)^{1/2}`) with the reciprocal-height dual
`4 ↔ ¼` sends it to amplitudes `(0, -1, 1)`: the half-integer bank `θ(x/4) - θ(x) = Σ_m e^{-π(m+½)²x}`
(no constant mode). No twisted Poisson and no ζ functional equation enter.

* `etaHelixBank`, `etaAntiHelixBank` (the latter read at the reflected height `1/x`), with values
  `etaHelixBank_eq : 2θ(4x) - θ(x)`, `etaAntiHelixBank_eq : θ(x/4) - θ(x)`.
* `eta_native_reflection`: `etaHelixBank (1/x) = x^{1/2}·etaAntiHelixBank x`: the native 3D reflection at `1/x`.
* `etaPair`: the pair, `k = ½`, `ε = 1`, `f₀ = 1` (the zero mode's booking), `g₀ = 0`.
* `eta_two_ended_cut`: for every cut `c > 0` (`w ≠ 0, ½`), exactly,
  `etaPair.Λ w = helixStrandAt etaPair c w + helixStrandAt etaPair.symm (1/c) (½ - w) - c^w/w`:
  the η-routed helix strand above `c`, the half-integer anti-helix strand above `1/c`, and ONE booking.
  The anti-helix here is a different bank, not the J-image of the helix.
* `etaPair_Λ_eq`: `etaPair.Λ w = (2·4^{-w} - 1)·nativePair.Λ w` for `w ≠ 0, ½`. With `w = s/2` the factor is
  `2^{1-s} - 1`, the conductor fold multiplier, produced by the bank's own heights and amplitudes.
* `riemannZeta_eq_zero_iff_eta_two_ended`: at height `Z` and every cut `c > 0`,
  `ζ(½ + i·log Z) = 0 ⟺ helixStrandAt etaPair c w + helixStrandAt etaPair.symm (1/c) (½ - w) - c^w/w = 0`,
  `w = (½ + i·log Z)/2`.

Scope: the completed (Mellin) fiber of the η-routed indexed bank. The `smoothEntry` head fiber of
`CarrierHeadFiniteFiber` is a different window and is not identified here; `FocalEvent` is unchanged.
-/

open Complex Set MeasureTheory Filter Topology Asymptotics

noncomputable section

namespace CriticalLinePhasor.HelixTwoEndedEta

open CriticalLinePhasor.GlobalHelix CriticalLinePhasor.HelixTwoEndedClosure
  CriticalLinePhasor.HelixTwoEndedNative

/-! ## The indexed bank -/

/-- Index heights `(4, 1, ¼)`. -/
def etaHeights : Fin 3 → ℝ := ![4, 1, 1 / 4]

/-- The η routing as amplitudes on the index heights: `2θ(4x) - θ(x)`. -/
def etaAmps : Fin 3 → ℂ := ![2, -1, 0]

/-- The reciprocal-height dual: `4 ↔ ¼`, `1` fixed. -/
def etaDual : Fin 3 ≃ Fin 3 := Equiv.swap 0 2

theorem etaHeights_pos : ∀ i, 0 < etaHeights i := by
  intro i
  fin_cases i <;> simp [etaHeights]

theorem etaHeights_recip : ∀ i, etaHeights (etaDual.symm i) = (etaHeights i)⁻¹ := by
  intro i
  fin_cases i <;> simp [etaHeights, etaDual, Equiv.swap_apply_def]

theorem rpow_four_half : (4 : ℝ) ^ (1 / 2 : ℝ) = 2 := by
  rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
  norm_num

theorem rpow_quarter_half : (4⁻¹ : ℝ) ^ (2⁻¹ : ℝ) = 2⁻¹ := by
  rw [Real.inv_rpow (by norm_num), show (2⁻¹ : ℝ) = 1 / 2 by norm_num, rpow_four_half]
  norm_num

/-- The dual amplitudes produced by the native reflection: `(0, -1, 1)`. -/
theorem etaDualAmps :
    gaussianPoissonDualAmplitude etaAmps etaHeights etaDual = ![0, -1, 1] := by
  funext i
  fin_cases i <;>
    simp [gaussianPoissonDualAmplitude, etaAmps, etaHeights, etaDual, Equiv.swap_apply_def,
      rpow_quarter_half]

/-- The η-routed helix bank on the 3D helix. -/
def etaHelixBank (x : ℝ) : ℂ := indexedGaussian3DBankReadout etaAmps etaHeights x

/-- The anti-helix bank of the η routing: the transformed 3D bank, read at the reflected height `1/x`. -/
def etaAntiHelixBank (x : ℝ) : ℂ := indexedGaussian3DTransformedReadout etaAmps etaHeights etaDual (1 / x)

theorem etaHelixBank_eq {x : ℝ} (hx : 0 < x) :
    etaHelixBank x = 2 * (gaussianLatticeTheta (4 * x) : ℂ) - (gaussianLatticeTheta x : ℂ) := by
  unfold etaHelixBank
  rw [indexedGaussian3DBankReadout_eq_theta _ _ etaHeights_pos hx, indexedTheta, tsum_fintype,
    Fin.sum_univ_three]
  simp [etaAmps, etaHeights]
  ring

theorem etaAntiHelixBank_eq {x : ℝ} (hx : 0 < x) :
    etaAntiHelixBank x = (gaussianLatticeTheta (1 / 4 * x) : ℂ) - (gaussianLatticeTheta x : ℂ) := by
  unfold etaAntiHelixBank
  rw [indexedGaussian3DTransformedReadout_eq_theta _ _ _ etaHeights_pos (one_div_pos.mpr hx),
    etaDualAmps, one_div_one_div, indexedTheta, tsum_fintype, Fin.sum_univ_three]
  simp [etaHeights]
  ring

/-- **The native 3D reflection carries the η routing to the half-integer bank.** -/
theorem eta_native_reflection {x : ℝ} (hx : 0 < x) :
    etaHelixBank (1 / x) = ((x ^ (1 / 2 : ℝ) : ℝ) : ℂ) * etaAntiHelixBank x := by
  have h := indexedGaussian3D_globalHelixReflection etaAmps etaHeights etaDual etaHeights_pos
    etaHeights_recip (one_div_pos.mpr hx)
  unfold etaHelixBank etaAntiHelixBank
  rw [h]
  congr 2
  rw [one_div x, Real.inv_rpow hx.le, one_div, inv_inv]

theorem theta_continuousOn_mul {H : ℝ} (hH : 0 < H) :
    ContinuousOn (fun x : ℝ => (gaussianLatticeTheta (H * x) : ℂ)) (Ioi 0) :=
  continuous_ofReal.comp_continuousOn
    (gaussianLatticeTheta_continuousOn.comp (continuousOn_const.mul continuousOn_id)
      fun x (hx : 0 < x) => show 0 < H * x from mul_pos hH hx)

theorem etaHelixBank_continuousOn : ContinuousOn etaHelixBank (Ioi 0) := by
  have h1 := theta_continuousOn_mul (show (0 : ℝ) < 4 by norm_num)
  have h2 := theta_continuousOn_mul (show (0 : ℝ) < 1 by norm_num)
  simp only [one_mul] at h2
  exact ((continuousOn_const.mul h1).sub h2).congr fun x hx => etaHelixBank_eq hx

theorem etaAntiHelixBank_continuousOn : ContinuousOn etaAntiHelixBank (Ioi 0) := by
  have h1 := theta_continuousOn_mul (show (0 : ℝ) < 1 / 4 by norm_num)
  have h2 := theta_continuousOn_mul (show (0 : ℝ) < 1 by norm_num)
  simp only [one_mul] at h2
  exact (h1.sub h2).congr fun x hx => etaAntiHelixBank_eq hx

/-- **The η-routed two-ended pair**, from the native 3D involution. -/
def etaPair : WeakFEPair ℂ where
  f := etaHelixBank
  g := etaAntiHelixBank
  k := 1 / 2
  ε := 1
  f₀ := 1
  g₀ := 0
  hf_int := etaHelixBank_continuousOn.locallyIntegrableOn measurableSet_Ioi
  hg_int := etaAntiHelixBank_continuousOn.locallyIntegrableOn measurableSet_Ioi
  hk := one_half_pos
  hε := one_ne_zero
  h_feq x hx := by
    rw [eta_native_reflection hx, one_mul, smul_eq_mul]
  hf_top r := by
    have h4 := (gaussianLatticeTheta_mul_sub_one_rapid (show (0 : ℝ) < 4 by norm_num) r).const_mul_left 2
    refine (h4.sub (gaussianLatticeTheta_sub_one_rapid r)).congr' ?_ EventuallyEq.rfl
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [etaHelixBank_eq hx]
    ring
  hg_top r := by
    refine ((gaussianLatticeTheta_mul_sub_one_rapid (show (0 : ℝ) < 1 / 4 by norm_num) r).sub
      (gaussianLatticeTheta_sub_one_rapid r)).congr' ?_ EventuallyEq.rfl
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [etaAntiHelixBank_eq hx]
    ring

/-- **The exact η-routed two-ended split at every cut**: one booking (the origin's), and the half-integer
anti-helix strand above `1/c`. -/
theorem eta_two_ended_cut {c : ℝ} (hc : 0 < c) {w : ℂ} (hw0 : w ≠ 0) (hwk : w ≠ 1 / 2) :
    etaPair.Λ w = helixStrandAt etaPair c w + helixStrandAt etaPair.symm c⁻¹ (1 / 2 - w)
      - (c : ℂ) ^ w / w := by
  have hk : w ≠ (etaPair.k : ℂ) := by
    show w ≠ ((1 / 2 : ℝ) : ℂ)
    push_cast
    exact hwk
  rw [Λ_two_ended_cut etaPair hc hw0 hk]
  simp only [etaPair]
  push_cast
  ring

/-! ## The fold multiplier from the bank's own heights -/

theorem etaPair_Λ_eq_of_re {w : ℂ} (hw : 1 / 2 < w.re) :
    etaPair.Λ w = (2 * (4 : ℂ) ^ (-w) - 1) * nativePair.Λ w := by
  have hkη : etaPair.k < w.re := by simpa [etaPair] using hw
  have hkθ : nativePair.k < w.re := by simpa [nativePair] using hw
  have hη := (etaPair.hasMellin hkη).2
  have hθ := nativePair.hasMellin hkθ
  set g : ℝ → ℂ := fun x => nativePair.f x - nativePair.f₀ with hg
  have hconv : MellinConvergent g w := hθ.1
  have hconv4 : MellinConvergent (fun x => g (4 * x)) w :=
    (MellinConvergent.comp_mul_left (show (0 : ℝ) < 4 by norm_num)).mpr hconv
  have heq : mellin (fun x => etaPair.f x - etaPair.f₀) w =
      mellin (fun x => 2 * g (4 * x) - g x) w := by
    unfold mellin
    refine setIntegral_congr_fun measurableSet_Ioi fun x (hx : 0 < x) => ?_
    show (x : ℂ) ^ (w - 1) • (etaHelixBank x - 1) =
      (x : ℂ) ^ (w - 1) • (2 * (helixBank (4 * x) - 1) - (helixBank x - 1))
    rw [etaHelixBank_eq hx, helixBank_eq (by positivity), helixBank_eq hx]
    ring_nf
  rw [← hη, heq]
  have hsplit : mellin (fun x => 2 * g (4 * x) - g x) w =
      2 * mellin (fun x => g (4 * x)) w - mellin g w := by
    have h1 : IntegrableOn (fun t : ℝ => 2 * ((t : ℂ) ^ (w - 1) • g (4 * t))) (Ioi 0) :=
      Integrable.const_mul hconv4 2
    have h2 : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (w - 1) • g t) (Ioi 0) := hconv
    calc mellin (fun x => 2 * g (4 * x) - g x) w
        = ∫ t in Ioi (0 : ℝ), (2 * ((t : ℂ) ^ (w - 1) • g (4 * t)) - (t : ℂ) ^ (w - 1) • g t) := by
          unfold mellin
          refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
          simp only [smul_eq_mul]
          ring
      _ = 2 * (∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (w - 1) • g (4 * t)) -
            ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (w - 1) • g t := by
          rw [integral_sub h1 h2, integral_const_mul]
      _ = 2 * mellin (fun x => g (4 * x)) w - mellin g w := rfl
  rw [hsplit, mellin_comp_mul_left _ _ (show (0 : ℝ) < 4 by norm_num), ← hθ.2, smul_eq_mul]
  push_cast
  ring

/-- **The η pair's completed transform is the fold multiplier times the Gaussian one**, for `w ≠ 0, ½`. -/
theorem etaPair_Λ_eq {w : ℂ} (hw0 : w ≠ 0) (hwk : w ≠ 1 / 2) :
    etaPair.Λ w = (2 * (4 : ℂ) ^ (-w) - 1) * nativePair.Λ w := by
  set S : Set ℂ := {0, 1 / 2} with hS
  have hSc : S.Countable := (Set.toFinite S).countable
  have hU : IsPreconnected Sᶜ :=
    (hSc.isConnected_compl_of_one_lt_rank (by rw [Complex.rank_real_complex]; norm_num)).isPreconnected
  have hUo : IsOpen Sᶜ := (Set.toFinite S).isClosed.isOpen_compl
  have hmem : ∀ {z : ℂ}, z ∈ Sᶜ → z ≠ 0 ∧ z ≠ 1 / 2 := fun {z} hz => by
    simp only [hS, mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or] at hz
    exact hz
  have hf : AnalyticOnNhd ℂ etaPair.Λ Sᶜ := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hUo
    exact (etaPair.differentiableAt_Λ (Or.inl (hmem hz).1) (Or.inr rfl)).differentiableWithinAt
  have hg : AnalyticOnNhd ℂ (fun z => (2 * (4 : ℂ) ^ (-z) - 1) * nativePair.Λ z) Sᶜ := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hUo
    have hz := hmem hz
    have hΛ : DifferentiableAt ℂ nativePair.Λ z :=
      nativePair.differentiableAt_Λ (Or.inl hz.1)
        (Or.inl (by show z ≠ ((1 / 2 : ℝ) : ℂ); push_cast; exact hz.2))
    have hc : DifferentiableAt ℂ (fun z : ℂ => (4 : ℂ) ^ (-z)) z :=
      (differentiableAt_id.neg).const_cpow (Or.inl (by norm_num))
    exact (((differentiableAt_const _).mul hc).sub (differentiableAt_const _)).mul hΛ
      |>.differentiableWithinAt
  have h1 : (1 : ℂ) ∈ Sᶜ := by
    simp only [hS, mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
    norm_num
  have hev : etaPair.Λ =ᶠ[𝓝 (1 : ℂ)] fun z => (2 * (4 : ℂ) ^ (-z) - 1) * nativePair.Λ z := by
    have hopen : IsOpen {z : ℂ | 1 / 2 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds (show (1 / 2 : ℝ) < (1 : ℂ).re by norm_num)] with z hz
    exact etaPair_Λ_eq_of_re hz
  have hz : w ∈ Sᶜ := by
    simp only [hS, mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
    exact ⟨hw0, hwk⟩
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg hU h1 hev hz

/-! ## The readout -/

/-- **At height `Z`, at every cut: the η-routed two-ended closure is the zero.** -/
theorem riemannZeta_eq_zero_iff_eta_two_ended (Z : ℝ) {c : ℝ} (hc : 0 < c) :
    riemannZeta (1 / 2 + (Real.log Z : ℂ) * I) = 0 ↔
      helixStrandAt etaPair c ((1 / 2 + (Real.log Z : ℂ) * I) / 2)
        + helixStrandAt etaPair.symm c⁻¹ (1 / 2 - (1 / 2 + (Real.log Z : ℂ) * I) / 2)
        - (c : ℂ) ^ ((1 / 2 + (Real.log Z : ℂ) * I) / 2) / ((1 / 2 + (Real.log Z : ℂ) * I) / 2) = 0 := by
  set s : ℂ := 1 / 2 + (Real.log Z : ℂ) * I with hsdef
  have hs : s.re = 1 / 2 := by simp [hsdef]
  have hs0 : s ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    rw [hs] at this
    norm_num at this
  have hw0 : s / 2 ≠ 0 := div_ne_zero hs0 two_ne_zero
  have hwk : s / 2 ≠ 1 / 2 := by
    intro h
    have := congrArg Complex.re h
    rw [Complex.div_ofNat_re, hs] at this
    norm_num at this
  have hfold : 2 * (4 : ℂ) ^ (-(s / 2)) - 1 ≠ 0 := by
    intro h
    have h2 : (4 : ℂ) ^ (-(s / 2)) = 1 / 2 := by linear_combination h / 2
    have hn := congrArg norm h2
    rw [show (4 : ℂ) = ((4 : ℝ) : ℂ) by norm_num,
      Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num)] at hn
    have hre : (-(s / 2)).re = -(1 / 4) := by
      rw [Complex.neg_re, Complex.div_ofNat_re, hs]
      norm_num
    rw [hre, Real.rpow_neg (by norm_num)] at hn
    have h4 : (4 : ℝ) ^ (1 / 4 : ℝ) = Real.sqrt 2 := by
      rw [Real.sqrt_eq_rpow, show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
      norm_num
    rw [h4] at hn
    have hsq : Real.sqrt 2 = 2 := by
      have : (Real.sqrt 2)⁻¹ = 1 / 2 := by simpa using hn
      have := congrArg (·⁻¹) this
      simpa using this
    have := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    rw [hsq] at this
    norm_num at this
  have hΓ : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by rw [hs]; norm_num)
  rw [← eta_two_ended_cut hc hw0 hwk, etaPair_Λ_eq hw0 hwk, mul_eq_zero, or_iff_right hfold,
    nativePair_Λ, riemannZeta_def_of_ne_zero hs0, div_eq_zero_iff, or_iff_left hΓ,
    completedRiemannZeta, HurwitzZeta.completedHurwitzZetaEven, div_eq_zero_iff,
    or_iff_left two_ne_zero]

end CriticalLinePhasor.HelixTwoEndedEta

end

#print axioms CriticalLinePhasor.HelixTwoEndedEta.etaDualAmps
#print axioms CriticalLinePhasor.HelixTwoEndedEta.eta_native_reflection
#print axioms CriticalLinePhasor.HelixTwoEndedEta.etaPair
#print axioms CriticalLinePhasor.HelixTwoEndedEta.eta_two_ended_cut
#print axioms CriticalLinePhasor.HelixTwoEndedEta.etaPair_Λ_eq
#print axioms CriticalLinePhasor.HelixTwoEndedEta.riemannZeta_eq_zero_iff_eta_two_ended
