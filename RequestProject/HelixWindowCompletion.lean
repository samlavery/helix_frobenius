import RequestProject.HelixTwoEndedEta
import RequestProject.FocalEventProjection

/-!
# The exact native completion of the smoothEntry head fiber (ledger 1257)

Heights: `Z` is the event's physical height (chart readout `log Z`); `N` is the head, the number of sites the
fiber has grown (at the event `N = physicalHead (log Z) ≈ 9Z²`); `x` is the height along the helix at which a
bank is read.

The event's own head fiber is `finiteFiber N s = Σ_{k<⌈N⌉} (-1)^k φ((k+1)/N) (k+1)^{-s}` (`φ = smoothEntry`). Its
sites, amplitudes and window define a Gaussian bank on the helix, and its tail is built from that bank, the
compiled η banks of ledger 1255 (`etaHelixBank`, `etaAntiHelixBank`), and the origin reflection. η is not used
to define the tail; it appears only in the last readout step.

* `windowBank N x = 1 - 2 Σ_k (-1)^k φ((k+1)/N) e^{-π(k+1)²x}`: the head's Gaussian bank, the zero mode
  `n = 0` included (`φ(0) = 1`). It is the windowed version of `etaHelixBank` (`2θ(4x) - θ(x)`).
* `windowAntiBank N u = u^{-1/2}·windowBank N (1/u)`: the head's bank under the origin reflection (the
  normalization of `eta_native_reflection`).
* `mellin_head`: `mellin (1 - windowBank N) w = 2π^{-w}Γ(w)·finiteFiber N (2w)` for `Re w > 0` (finite sum;
  Mathlib's `hasSum_mellin`).
* `head_two_ended`: the head fiber's own two-ended form at every cut `c > 0`,
  `2π^{-w}Γ(w)·finiteFiber N (2w) = ∫_{x>c} x^{w-1}(1 - windowBank) + c^w/w - ∫_{u>1/c} u^{½-w-1} windowAntiBank`.
* `upperCorrection N c w = ∫_{x>c} x^{w-1}(windowBank N x - etaHelixBank x)`: the helix correction above the cut.
  `lowerCorrection N c w = ∫_{u>1/c} u^{½-w-1}(windowAntiBank N u - etaAntiHelixBank u)`: the reflected
  anti-helix correction.
  `windowTail N c s = π^{s/2}/(2Γ(s/2))·(upperCorrection + lowerCorrection)` at `w = s/2`.
* `window_completion`: **for `Re s > 0`, `s ≠ 1`, every head `N > 0` and every cut `c > 0`, exactly,
  `finiteFiber N s + windowTail N c s = (1 - 2^{1-s})·ζ(s)`.** `windowTail_cut_independent` follows.
* Arrows into the focal geometry, with `FocalEvent` unchanged:
  - `headSum_window_completion`: the η-routed power-law head sum at the native head `physicalHead y`, plus
    the tail, is `(1 - 2^{1-s})ζ(s)` at `s = σ + iy`.
  - `head_two_ended_closure_iff`: at `σ = ½`, `headSum + windowTail = 0 ⟺ ζ(½ + iy) = 0`.
  - `FocalEvent.windowTail_eq`: an event of the η-routed power-law type (exact one-sided head cancellation)
    has tail equal to the analytic value: the one-sided cancellation's whole discrepancy is the tail.

Not in this file: the Fourier form of `windowAntiBank` (the half-integer bank blurred by the window's Fourier
transform, checked numerically in ledger 1256). That needs the general Poisson summation formula; the indexed
3D reflection covers Gaussian banks only.
-/

open Complex Set MeasureTheory Filter Topology

noncomputable section

namespace CriticalLinePhasor.HelixWindowCompletion

open CriticalLinePhasor CriticalLinePhasor.CarrierHeadFiniteFiber CriticalLinePhasor.HelixTwoEndedClosure
  CriticalLinePhasor.HelixTwoEndedNative CriticalLinePhasor.HelixTwoEndedEta CriticalLinePhasor.GlobalHelix

/-! ## The head's bank -/

/-- The head's site coefficient: site `k+1` carries `(-1)^k φ((k+1)/N)`. -/
def headCoeff (N : ℝ) (k : ℕ) : ℂ := (-1 : ℂ) ^ k * (smoothEntry (((k + 1 : ℕ) : ℝ) / N) : ℂ)

/-- The Gaussian height rate of site `k+1`. -/
def siteRate (k : ℕ) : ℝ := Real.pi * ((k + 1 : ℕ) : ℝ) ^ 2

theorem siteRate_pos (k : ℕ) : 0 < siteRate k := by
  unfold siteRate
  positivity

theorem finiteFiber_eq_sum (N : ℝ) (s : ℂ) :
    finiteFiber N s = ∑ k ∈ Finset.range ⌈N⌉₊,
      headCoeff N k * Complex.exp (-s * (Real.log ((k + 1 : ℕ) : ℝ) : ℂ)) := rfl

/-- **The head's Gaussian bank** (the zero mode `n = 0` included). -/
def windowBank (N x : ℝ) : ℂ :=
  1 - 2 * ∑ k ∈ Finset.range ⌈N⌉₊, headCoeff N k * ((Real.exp (-siteRate k * x) : ℝ) : ℂ)

/-- **The head's bank under the origin reflection**, read at height `u`. -/
def windowAntiBank (N u : ℝ) : ℂ := ((u ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * windowBank N u⁻¹

theorem one_sub_windowBank (N x : ℝ) :
    1 - windowBank N x = ∑ k ∈ Finset.range ⌈N⌉₊, 2 * headCoeff N k * ((Real.exp (-siteRate k * x) : ℝ) : ℂ) := by
  unfold windowBank
  rw [sub_sub_cancel, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- `1/(π(k+1)²)^w = π^{-w} (k+1)^{-2w}`, in exponential form. -/
theorem inv_siteRate_cpow (k : ℕ) (w : ℂ) :
    1 / ((siteRate k : ℝ) : ℂ) ^ w =
      (Real.pi : ℂ) ^ (-w) * Complex.exp (-(2 * w) * (Real.log ((k + 1 : ℕ) : ℝ) : ℂ)) := by
  have hp := siteRate_pos k
  have hk : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr hp.ne'),
    cpow_def_of_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero), ← ofReal_log hp.le,
    ← ofReal_log Real.pi_pos.le, siteRate, Real.log_mul Real.pi_ne_zero (by positivity), Real.log_pow,
    one_div, ← Complex.exp_neg, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- **The finite Mellin identity**: the head fiber is the Mellin transform of its bank. -/
theorem mellin_head (N : ℝ) {w : ℂ} (hw : 0 < w.re) :
    mellin (fun x => 1 - windowBank N x) w = 2 * (Real.pi : ℂ) ^ (-w) * Gamma w * finiteFiber N (2 * w) := by
  set M := ⌈N⌉₊
  have h := hasSum_mellin (ι := Fin M) (a := fun i => 2 * headCoeff N i) (p := fun i => siteRate i)
    (F := fun x => 1 - windowBank N x) (s := w) (fun i => Or.inr (siteRate_pos i)) hw
    (fun t _ => by
      rw [one_sub_windowBank, ← Fin.sum_univ_eq_sum_range]
      exact hasSum_fintype _)
    (hasSum_fintype _).summable
  rw [h.tsum_eq.symm, tsum_fintype, Fin.sum_univ_eq_sum_range (fun i => Gamma w * (2 * headCoeff N i) /
    ((siteRate i : ℝ) : ℂ) ^ w), finiteFiber_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [div_eq_mul_one_div, inv_siteRate_cpow]
  ring

theorem integrableOn_cpow_exp {w : ℂ} (hw : 0 < w.re) {p : ℝ} (hp : 0 < p) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (w - 1) * ((Real.exp (-p * t) : ℝ) : ℂ)) (Ioi 0) := by
  have := Complex.GammaIntegral_convergent hw
  rw [← mul_zero p, ← integrableOn_Ioi_comp_mul_left_iff _ _ hp] at this
  refine IntegrableOn.congr_fun (this.const_mul (1 / (p : ℂ) ^ (w - 1)))
    (fun t (ht : 0 < t) => ?_) measurableSet_Ioi
  have hne : ((p : ℝ) : ℂ) ^ (w - 1) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff, not_and_or]
    exact Or.inl (ofReal_ne_zero.mpr hp.ne')
  rw [ofReal_mul, mul_cpow_ofReal_nonneg hp.le ht.le, neg_mul]
  field_simp

theorem integrableOn_head (N : ℝ) {w : ℂ} (hw : 0 < w.re) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ (w - 1) * (1 - windowBank N x)) (Ioi 0) := by
  have h : (fun x : ℝ => (x : ℂ) ^ (w - 1) * (1 - windowBank N x)) =
      fun x : ℝ => ∑ k ∈ Finset.range ⌈N⌉₊,
        2 * headCoeff N k * ((x : ℂ) ^ (w - 1) * ((Real.exp (-siteRate k * x) : ℝ) : ℂ)) := by
    funext x
    rw [one_sub_windowBank, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [h]
  exact integrable_finsetSum _ fun k _ => (integrableOn_cpow_exp hw (siteRate_pos k)).const_mul _

/-! ## The origin reflection of the lower slab -/

/-- `∫_{(0,c]} x^{w-1} f(x) dx = ∫_{u>1/c} u^{-w-1} f(1/u) du`. -/
theorem lower_reflect (f : ℝ → ℂ) {c : ℝ} (hc : 0 < c) (w : ℂ) :
    ∫ x in Ioc 0 c, (x : ℂ) ^ (w - 1) * f x = ∫ u in Ioi c⁻¹, (u : ℂ) ^ (-w - 1) * f u⁻¹ := by
  set F : ℝ → ℂ := (Ioc 0 c).indicator f with hF
  have h1 : mellin F w = ∫ x in Ioc 0 c, (x : ℂ) ^ (w - 1) * f x := by
    unfold mellin
    have h : (fun t : ℝ => (t : ℂ) ^ (w - 1) • F t) =
        (Ioc 0 c).indicator (fun t : ℝ => (t : ℂ) ^ (w - 1) * f t) := by
      funext t
      by_cases ht : t ∈ Ioc 0 c
      · simp [hF, indicator_of_mem ht, smul_eq_mul]
      · simp [hF, indicator_of_notMem ht]
    have hsub : Ioc 0 c ⊆ Ioi (0 : ℝ) := fun x hx => hx.1
    rw [h, setIntegral_indicator measurableSet_Ioc, inter_eq_right.mpr hsub]
  have key := mellin_comp_inv (fun u => F u⁻¹) w
  simp only [inv_inv] at key
  rw [← h1, key]
  unfold mellin
  have h2 : EqOn (fun u : ℝ => (u : ℂ) ^ (-w - 1) • F u⁻¹)
      ((Ici c⁻¹).indicator (fun u : ℝ => (u : ℂ) ^ (-w - 1) * f u⁻¹)) (Ioi 0) := by
    intro u (hu : 0 < u)
    have hiff : u⁻¹ ∈ Ioc 0 c ↔ u ∈ Ici c⁻¹ := by
      constructor
      · rintro ⟨_, h2⟩
        exact (inv_le_comm₀ hu hc).mp h2
      · intro h
        exact ⟨inv_pos.mpr hu, (inv_le_comm₀ hu hc).mpr h⟩
    by_cases hm : u ∈ Ici c⁻¹
    · simp [hF, indicator_of_mem (hiff.mpr hm), indicator_of_mem hm, smul_eq_mul]
    · have hn : u⁻¹ ∉ Ioc 0 c := fun h => hm (hiff.mp h)
      simp [hF, indicator_of_notMem hn, indicator_of_notMem hm]
  have hsub : Ici c⁻¹ ⊆ Ioi (0 : ℝ) := fun x hx => lt_of_lt_of_le (inv_pos.mpr hc) hx
  rw [setIntegral_congr_fun measurableSet_Ioi h2, setIntegral_indicator measurableSet_Ici,
    inter_eq_right.mpr hsub, integral_Ici_eq_integral_Ioi]

theorem cpow_reflect_weight {u : ℝ} (hu : 0 < u) (w : ℂ) :
    (u : ℂ) ^ (-w - 1) = (u : ℂ) ^ (1 / 2 - w - 1) * ((u ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
  rw [ofReal_cpow hu.le, ← cpow_add _ _ (ofReal_ne_zero.mpr hu.ne')]
  congr 1
  push_cast
  ring

/-- **The head fiber's own two-ended form, at every cut.** -/
theorem head_two_ended (N : ℝ) {c : ℝ} (hc : 0 < c) {w : ℂ} (hw : 0 < w.re) :
    2 * (Real.pi : ℂ) ^ (-w) * Gamma w * finiteFiber N (2 * w) =
      (∫ x in Ioi c, (x : ℂ) ^ (w - 1) * (1 - windowBank N x)) + (c : ℂ) ^ w / w
        - ∫ u in Ioi c⁻¹, (u : ℂ) ^ (1 / 2 - w - 1) * windowAntiBank N u := by
  have hint := integrableOn_head N hw
  have hlow : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (w - 1) * (1 - windowBank N x)) (Ioc 0 c) :=
    hint.mono_set fun x hx => hx.1
  have hpow : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (w - 1)) (Ioc 0 c) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hc.le]
    exact intervalIntegral.intervalIntegrable_cpow' (by simp; linarith)
  have hB : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (w - 1) * windowBank N x) (Ioc 0 c) := by
    refine (hpow.sub hlow).congr_fun (fun x _ => ?_) measurableSet_Ioc
    simp only [Pi.sub_apply]
    ring
  have hw0 : w ≠ 0 := fun h => by simp [h] at hw
  rw [← mellin_head N hw]
  unfold mellin
  simp only [smul_eq_mul]
  rw [← Ioc_union_Ioi_eq_Ioi hc.le, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hlow
    (hint.mono_set (Ioi_subset_Ioi hc.le))]
  have hsplit : ∫ x in Ioc 0 c, (x : ℂ) ^ (w - 1) * (1 - windowBank N x) =
      (∫ x in Ioc 0 c, (x : ℂ) ^ (w - 1)) - ∫ x in Ioc 0 c, (x : ℂ) ^ (w - 1) * windowBank N x := by
    rw [← integral_sub hpow hB]
    refine setIntegral_congr_fun measurableSet_Ioc fun x _ => ?_
    ring
  have hpowint : ∫ x in Ioc 0 c, (x : ℂ) ^ (w - 1) = (c : ℂ) ^ w / w := by
    rw [← intervalIntegral.integral_of_le hc.le, integral_cpow (Or.inl (by simp; linarith))]
    simp [sub_add_cancel, Complex.zero_cpow hw0]
  have hrefl : ∫ x in Ioc 0 c, (x : ℂ) ^ (w - 1) * windowBank N x =
      ∫ u in Ioi c⁻¹, (u : ℂ) ^ (1 / 2 - w - 1) * windowAntiBank N u := by
    rw [lower_reflect (windowBank N) hc w]
    refine setIntegral_congr_fun measurableSet_Ioi fun u (hu : c⁻¹ < u) => ?_
    have hu0 : 0 < u := (inv_pos.mpr hc).trans hu
    rw [cpow_reflect_weight hu0 w, windowAntiBank]
    ring
  rw [hsplit, hpowint, hrefl]
  ring

/-! ## The η readout of the compiled pair -/

theorem fold_cpow (w : ℂ) : 2 * (4 : ℂ) ^ (-w) = (2 : ℂ) ^ (1 - 2 * w) := by
  have h4 : (4 : ℂ) = ((4 : ℝ) : ℂ) := by norm_num
  have h2 : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_num
  rw [h4, h2, cpow_def_of_ne_zero (ofReal_ne_zero.mpr (by norm_num : (4 : ℝ) ≠ 0)),
    cpow_def_of_ne_zero (ofReal_ne_zero.mpr (by norm_num : (2 : ℝ) ≠ 0)),
    ← ofReal_log (by norm_num : (0 : ℝ) ≤ 4), ← ofReal_log (by norm_num : (0 : ℝ) ≤ 2),
    show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  have he : ((2 : ℝ) : ℂ) = Complex.exp (Real.log 2 : ℂ) := by
    rw [← ofReal_exp, Real.exp_log (by norm_num)]
  conv_lhs => rw [he]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The compiled η pair's completed transform, read out: `-2π^{-w}Γ(w)·(1 - 2^{1-2w})ζ(2w)`. -/
theorem etaPair_Λ_readout {w : ℂ} (hw : 0 < w.re) (hw2 : w ≠ 1 / 2) :
    etaPair.Λ w = -(2 * (Real.pi : ℂ) ^ (-w) * Gamma w *
      ((1 - (2 : ℂ) ^ (1 - 2 * w)) * riemannZeta (2 * w))) := by
  have hw0 : w ≠ 0 := fun h => by simp [h] at hw
  have h2w : 2 * w ≠ 0 := mul_ne_zero two_ne_zero hw0
  have hΓℝ : Gammaℝ (2 * w) ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
  have hΛ : (HurwitzZeta.hurwitzEvenFEPair 0).Λ w = 2 * completedRiemannZeta (2 * w) := by
    rw [completedRiemannZeta, HurwitzZeta.completedHurwitzZetaEven,
      mul_div_cancel_left₀ _ (two_ne_zero : (2 : ℂ) ≠ 0)]
    ring
  have hz : completedRiemannZeta (2 * w) = Gammaℝ (2 * w) * riemannZeta (2 * w) := by
    rw [riemannZeta_def_of_ne_zero h2w, mul_div_cancel₀ _ hΓℝ]
  rw [etaPair_Λ_eq hw0 hw2, nativePair_Λ, hΛ, hz, Gammaℝ_def,
    show -(2 * w) / 2 = -w by ring, show 2 * w / 2 = w by ring, fold_cpow]
  ring

/-! ## The constructed tail and the exact completion -/

/-- The helix correction above the cut: windowed bank minus the native full alternating bank. -/
def upperCorrection (N c : ℝ) (w : ℂ) : ℂ :=
  ∫ x in Ioi c, (x : ℂ) ^ (w - 1) * (windowBank N x - etaHelixBank x)

/-- The reflected anti-helix correction above `1/c`: the head's reflected bank minus the native half-integer
bank. -/
def lowerCorrection (N c : ℝ) (w : ℂ) : ℂ :=
  ∫ u in Ioi c⁻¹, (u : ℂ) ^ (1 / 2 - w - 1) * (windowAntiBank N u - etaAntiHelixBank u)

/-- **The constructed tail** of the head fiber at the cut `c`. -/
def windowTail (N c : ℝ) (s : ℂ) : ℂ :=
  (Real.pi : ℂ) ^ (s / 2) / (2 * Gamma (s / 2)) * (upperCorrection N c (s / 2) + lowerCorrection N c (s / 2))

theorem windowBank_norm_le (N : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    ‖windowBank N x‖ ≤ 1 + 2 * ∑ k ∈ Finset.range ⌈N⌉₊, ‖headCoeff N k‖ := by
  unfold windowBank
  refine (norm_sub_le _ _).trans ?_
  rw [norm_one, norm_mul, Complex.norm_two]
  gcongr
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [norm_mul]
  have he : ‖((Real.exp (-siteRate k * x) : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (by nlinarith [siteRate_pos k])
  calc ‖headCoeff N k‖ * ‖((Real.exp (-siteRate k * x) : ℝ) : ℂ)‖ ≤ ‖headCoeff N k‖ * 1 :=
        mul_le_mul_of_nonneg_left he (norm_nonneg _)
    _ = ‖headCoeff N k‖ := mul_one _

theorem windowBank_continuous (N : ℝ) : Continuous (windowBank N) := by
  unfold windowBank
  fun_prop

theorem integrableOn_windowAnti (N : ℝ) {c : ℝ} (hc : 0 < c) {w : ℂ} (hw : 0 < w.re) :
    IntegrableOn (fun u : ℝ => (u : ℂ) ^ (1 / 2 - w - 1) * windowAntiBank N u) (Ioi c⁻¹) := by
  set K := 1 + 2 * ∑ k ∈ Finset.range ⌈N⌉₊, ‖headCoeff N k‖
  have hci : 0 < c⁻¹ := inv_pos.mpr hc
  have hg : IntegrableOn (fun u : ℝ => (u : ℂ) ^ (-w - 1)) (Ioi c⁻¹) :=
    integrableOn_Ioi_cpow_of_lt (by simp; linarith) hci
  have heq : EqOn (fun u : ℝ => (u : ℂ) ^ (1 / 2 - w - 1) * windowAntiBank N u)
      (fun u : ℝ => (u : ℂ) ^ (-w - 1) * windowBank N u⁻¹) (Ioi c⁻¹) := by
    intro u (hu : c⁻¹ < u)
    dsimp only
    rw [cpow_reflect_weight (hci.trans hu) w, windowAntiBank]
    ring
  refine IntegrableOn.congr_fun ?_ heq.symm measurableSet_Ioi
  refine Integrable.mono' (hg.norm.const_mul K) ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable (fun u (hu : c⁻¹ < u) => ?_) measurableSet_Ioi
    have hu0 : 0 < u := hci.trans hu
    exact ((Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr hu0.ne')).mul
      ((windowBank_continuous N).continuousAt.comp (continuousAt_inv₀ hu0.ne'))).continuousWithinAt
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun u (hu : c⁻¹ < u) => ?_)
    have hu0 : 0 < u := hci.trans hu
    rw [norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (windowBank_norm_le N (inv_pos.mpr hu0).le) (norm_nonneg _)

/-- **The exact native window completion.** For `Re s > 0`, `s ≠ 1`, every head `N > 0` and every cut `c > 0`:
the event's head fiber plus the constructed two-ended tail is `(1 - 2^{1-s})ζ(s)`. -/
theorem window_completion {N : ℝ} {c : ℝ} (hc : 0 < c) {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    finiteFiber N s + windowTail N c s = (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s := by
  set w := s / 2 with hwdef
  have hw : 0 < w.re := by rw [hwdef, Complex.div_ofNat_re]; linarith
  have hw2 : w ≠ 1 / 2 := fun h => hs1 (by rw [hwdef] at h; linear_combination 2 * h)
  have hs2 : s = 2 * w := by rw [hwdef]; ring
  have hΓ : Gamma w ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hw
  have hπ : (Real.pi : ℂ) ^ w * (Real.pi : ℂ) ^ (-w) = 1 := by
    rw [← cpow_add _ _ (ofReal_ne_zero.mpr Real.pi_ne_zero), add_neg_cancel, cpow_zero]
  -- the head's two-ended form and the compiled η cut theorem at the same cut
  have hH := head_two_ended N hc hw
  have hE := eta_two_ended_cut hc (fun h => by simp [h] at hw) hw2
  rw [etaPair_Λ_readout hw hw2] at hE
  -- the corrections as differences of strands
  have hU : upperCorrection N c w = -helixStrandAt etaPair c w
      - ∫ x in Ioi c, (x : ℂ) ^ (w - 1) * (1 - windowBank N x) := by
    have hS : IntegrableOn (fun x : ℝ => -((x : ℂ) ^ (w - 1) * (etaPair.f x - etaPair.f₀))) (Ioi c) :=
      (integrableOn_strand etaPair hc w).neg
    unfold upperCorrection helixStrandAt
    rw [← integral_neg, ← integral_sub hS ((integrableOn_head N hw).mono_set (Ioi_subset_Ioi hc.le))]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    show _ = -((x : ℂ) ^ (w - 1) * (etaHelixBank x - 1)) - _
    ring
  have hL : lowerCorrection N c w = (∫ u in Ioi c⁻¹, (u : ℂ) ^ (1 / 2 - w - 1) * windowAntiBank N u)
      - helixStrandAt etaPair.symm c⁻¹ (1 / 2 - w) := by
    unfold lowerCorrection helixStrandAt
    rw [← integral_sub (integrableOn_windowAnti N hc hw)
      (integrableOn_strand etaPair.symm (inv_pos.mpr hc) (1 / 2 - w))]
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    show _ = _ - (u : ℂ) ^ (1 / 2 - w - 1) * (etaAntiHelixBank u - 0)
    ring
  -- solve the linear system
  have key : upperCorrection N c w + lowerCorrection N c w =
      2 * (Real.pi : ℂ) ^ (-w) * Gamma w *
        ((1 - (2 : ℂ) ^ (1 - 2 * w)) * riemannZeta (2 * w) - finiteFiber N (2 * w)) := by
    rw [hU, hL]
    linear_combination hE + hH
  unfold windowTail
  rw [← hwdef, key, hs2]
  generalize hXdef : (1 - (2 : ℂ) ^ (1 - 2 * w)) * riemannZeta (2 * w) - finiteFiber N (2 * w) = X
  have h2Γ : (2 : ℂ) * Gamma w ≠ 0 := mul_ne_zero two_ne_zero hΓ
  have hfin : (Real.pi : ℂ) ^ w / (2 * Gamma w) * (2 * (Real.pi : ℂ) ^ (-w) * Gamma w * X) = X := by
    calc (Real.pi : ℂ) ^ w / (2 * Gamma w) * (2 * (Real.pi : ℂ) ^ (-w) * Gamma w * X)
        = ((Real.pi : ℂ) ^ w * (Real.pi : ℂ) ^ (-w)) * X * ((2 * Gamma w) / (2 * Gamma w)) := by ring
      _ = X := by rw [hπ, div_self h2Γ]; ring
  rw [hfin, ← hXdef]
  ring

/-- **The tail does not depend on the cut.** -/
theorem windowTail_cut_independent {N c c' : ℝ} (hc : 0 < c) (hc' : 0 < c') {s : ℂ} (hs : 0 < s.re)
    (hs1 : s ≠ 1) : windowTail N c s = windowTail N c' s := by
  have h1 := window_completion (N := N) hc hs hs1
  have h2 := window_completion (N := N) hc' hs hs1
  linear_combination h1 - h2

/-! ## Arrows into the focal geometry (`FocalEvent` unchanged) -/

open CriticalLinePhasor.FocalEventProjection CriticalLinePhasor.EisensteinWheelBank

/-- The η-routed power-law head sum at the native head is the head fiber. -/
theorem headSum_eq_finiteFiber (σ y : ℝ) :
    headSum Routing.eta.coeff (fun k => ((k : ℝ) + 1) ^ (-σ)) y =
      finiteFiber (physicalHead y) ((σ : ℂ) + (y : ℂ) * I) := by
  rw [← lawFiber_head_eq_headSum, FiberDetectorChain.lawFiber_eta]

/-- **The event's own head sum, completed exactly by the constructed tail.** -/
theorem headSum_window_completion {σ : ℝ} (hσ : 0 < σ) (y : ℝ) {c : ℝ} (hc : 0 < c)
    (hs1 : (σ : ℂ) + (y : ℂ) * I ≠ 1) :
    headSum Routing.eta.coeff (fun k => ((k : ℝ) + 1) ^ (-σ)) y +
        windowTail (physicalHead y) c ((σ : ℂ) + (y : ℂ) * I) =
      (1 - (2 : ℂ) ^ (1 - ((σ : ℂ) + (y : ℂ) * I))) * riemannZeta ((σ : ℂ) + (y : ℂ) * I) := by
  rw [headSum_eq_finiteFiber]
  exact window_completion hc (by simpa using hσ) hs1

/-- **The two-ended closure of the event's head at the native exponent**: head sum plus tail vanishes exactly
when `ζ(½ + iy) = 0`. -/
theorem head_two_ended_closure_iff (y : ℝ) {c : ℝ} (hc : 0 < c) :
    headSum Routing.eta.coeff (fun k => ((k : ℝ) + 1) ^ (-(1 / 2 : ℝ))) y +
        windowTail (physicalHead y) c (((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I) = 0 ↔
      riemannZeta (((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I) = 0 := by
  set s : ℂ := ((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I with hsdef
  have hs1 : s ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    norm_num [hsdef] at this
  have hfold : (1 : ℂ) - (2 : ℂ) ^ (1 - s) ≠ 0 := by
    intro h
    have h1 : (2 : ℂ) ^ (1 - s) = 1 := by linear_combination -h
    have hn := congrArg norm h1
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
      Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num), norm_one] at hn
    have hre : (1 - s).re = 1 / 2 := by norm_num [hsdef]
    rw [hre] at hn
    have : (1 : ℝ) < 2 ^ (1 / 2 : ℝ) := Real.one_lt_rpow (by norm_num) (by norm_num)
    linarith
  rw [headSum_window_completion (by norm_num) y hc hs1, mul_eq_zero, or_iff_right hfold]

/-- **An exact one-sided head cancellation, completed**: for an event of the η-routed power-law type, the tail
equals the analytic value. The one-sided cancellation's whole discrepancy is the tail. -/
theorem FocalEvent.windowTail_eq (e : FocalEvent) {σ : ℝ} (hσ : 0 < σ)
    (hw : e.w = Routing.eta.coeff) (ha : e.a = fun k : ℕ => ((k : ℝ) + 1) ^ (-σ)) {c : ℝ} (hc : 0 < c)
    (hs1 : (σ : ℂ) + (e.y : ℂ) * I ≠ 1) :
    windowTail (physicalHead e.y) c ((σ : ℂ) + (e.y : ℂ) * I) =
      (1 - (2 : ℂ) ^ (1 - ((σ : ℂ) + (e.y : ℂ) * I))) * riemannZeta ((σ : ℂ) + (e.y : ℂ) * I) := by
  have h := headSum_window_completion hσ e.y hc hs1
  have hcancel := e.cancel
  rw [hw, ha] at hcancel
  rw [hcancel, zero_add] at h
  exact h

end CriticalLinePhasor.HelixWindowCompletion

end

#print axioms CriticalLinePhasor.HelixWindowCompletion.mellin_head
#print axioms CriticalLinePhasor.HelixWindowCompletion.head_two_ended
#print axioms CriticalLinePhasor.HelixWindowCompletion.etaPair_Λ_readout
#print axioms CriticalLinePhasor.HelixWindowCompletion.window_completion
#print axioms CriticalLinePhasor.HelixWindowCompletion.windowTail_cut_independent
#print axioms CriticalLinePhasor.HelixWindowCompletion.headSum_window_completion
#print axioms CriticalLinePhasor.HelixWindowCompletion.head_two_ended_closure_iff
#print axioms CriticalLinePhasor.HelixWindowCompletion.FocalEvent.windowTail_eq
