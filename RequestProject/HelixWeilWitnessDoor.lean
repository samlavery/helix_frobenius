import RequestProject.WeilExplicitFormulaGauss
import RequestProject.HelixWeilWitnessNear

/-!
# The Weil witness, brick W3b: the pair profile is an admissible test, and the Gaussian-class door (ledger 1340)

The explicit formula for integrable line profiles (`weil_explicit_formula'`, 1339) is applied to the autocorrelation
`g = h ⋆ h̃` of the pair profile `h = pairProfile λ ρ₀` (1336). Verified here:

* `autocorr_pairProfile_continuous` — `g` is continuous (convolution of an integrable with a bounded continuous
  profile, `BddAbove.continuous_convolution_right_of_integrable`);
* `lineProfile_autocorr_integrable` — `g_σ` is integrable for every `σ` (the weighted convolution is the convolution
  of the weighted Gaussians, `Integrable.integrable_convolution`);
* `laplaceTest_autocorr_pairProfile_differentiable` — `F = −|N|²·D²` is entire;
* `laplaceTest_autocorr_pairProfile_decay` — `‖F(x + iT)‖ ≤ C/(1 + |T|)⁴` on any strip, from the height-Gaussian
  `‖D‖ ≤ 2e^{λ(A − (T−γ)²)}` and `(1 + |T|)⁴ ≤ 64(1+γ²)² e^{λ(T−γ)²}` for `λ ≥ 1`;
* `carrierSide_pair_eq_zeroSide` — the explicit formula at the pair profile;
* `CarrierPositivePair`, `LocalMaxExists`, `axis_of_carrierPositivePair`, `riemannHypothesis_of_carrierPositivePair`
  — **the Gaussian-class door**: carrier positivity on the pair profiles' autocorrelations, plus the existence of a
  locally maximal off-axis zero whenever an off-axis zero exists (Case B, 1337), put every zero on the axis.

The chain to RH is now: `CarrierPositivePair` (the leaf, carrier data only) + `LocalMaxExists` (the one classical
analytic point left in the witness) ⟹ RH, with the witness compiled end to end otherwise. No `sorry`, no `axiom`,
no window.
-/

open Complex MeasureTheory Filter Topology
open scoped Real ComplexConjugate Convolution

noncomputable section

namespace CriticalLinePhasor.HelixWeilWitness

open CriticalLinePhasor.ContourArgument CriticalLinePhasor.HelixCarrierWeil CriticalLinePhasor.WeilGauss

/-! ## Continuity and boundedness of the profiles -/

theorem gaussProfile_continuous (lam : ℝ) (ρ : ℂ) : Continuous (gaussProfile lam ρ) := by
  unfold gaussProfile; fun_prop

theorem pairProfile_continuous (lam : ℝ) (ρ₀ : ℂ) : Continuous (pairProfile lam ρ₀) := by
  unfold pairProfile; exact (gaussProfile_continuous lam ρ₀).sub (gaussProfile_continuous lam _)

/-- `‖gaussProfile λ ρ x‖ ≤ exp(λ(½ − Re ρ)²)` — complete the square. -/
theorem gaussProfile_norm_le {lam : ℝ} (hlam : 0 < lam) (ρ : ℂ) (x : ℝ) :
    ‖gaussProfile lam ρ x‖ ≤ Real.exp (lam * (1 / 2 - ρ.re) ^ 2) := by
  unfold gaussProfile
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have hre : (bcoef lam * (x : ℂ) ^ 2 + (1 / 2 - ρ) * x).re = -(1 / (4 * lam)) * x ^ 2 + (1 / 2 - ρ.re) * x := by
    unfold bcoef
    simp [Complex.add_re, Complex.mul_re, Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im, sq] <;> ring
  rw [hre]
  -- `−x²/(4λ) + c x ≤ λ c²` ⟸ `(x − 2λc)² ≥ 0`
  set c : ℝ := 1 / 2 - ρ.re with hc
  have h4 : 0 < 4 * lam := by positivity
  have key : (x - 2 * lam * c) ^ 2 / (4 * lam) ≥ 0 := by positivity
  have : -(1 / (4 * lam)) * x ^ 2 + c * x = lam * c ^ 2 - (x - 2 * lam * c) ^ 2 / (4 * lam) := by
    field_simp; ring
  rw [this]; linarith

theorem pairProfile_norm_le {lam : ℝ} (hlam : 0 < lam) (ρ₀ : ℂ) (x : ℝ) :
    ‖pairProfile lam ρ₀ x‖ ≤ Real.exp (lam * (1 / 2 - ρ₀.re) ^ 2) + Real.exp (lam * (1 / 2 - (1 - conj ρ₀).re) ^ 2) := by
  unfold pairProfile
  calc ‖gaussProfile lam ρ₀ x - gaussProfile lam (1 - conj ρ₀) x‖
      ≤ ‖gaussProfile lam ρ₀ x‖ + ‖gaussProfile lam (1 - conj ρ₀) x‖ := norm_sub_le _ _
    _ ≤ _ := add_le_add (gaussProfile_norm_le hlam ρ₀ x) (gaussProfile_norm_le hlam _ x)

theorem reflect_pairProfile_bddAbove {lam : ℝ} (hlam : 0 < lam) (ρ₀ : ℂ) :
    BddAbove (Set.range fun x : ℝ => ‖reflect (pairProfile lam ρ₀) x‖) := by
  refine ⟨Real.exp (lam * (1 / 2 - ρ₀.re) ^ 2) + Real.exp (lam * (1 / 2 - (1 - conj ρ₀).re) ^ 2), ?_⟩
  rintro _ ⟨x, rfl⟩
  show ‖reflect (pairProfile lam ρ₀) x‖ ≤ _
  unfold reflect
  rw [Complex.norm_conj]
  exact pairProfile_norm_le hlam ρ₀ (-x)

theorem pairProfile_integrable {lam : ℝ} (hlam : 0 < lam) (ρ₀ : ℂ) : Integrable (pairProfile lam ρ₀) := by
  have h := pairProfile_mul_exp_integrable hlam ρ₀ (1 / 2)
  refine h.congr ?_
  filter_upwards with x
  simp

theorem autocorr_pairProfile_continuous {lam : ℝ} (hlam : 0 < lam) (ρ₀ : ℂ) :
    Continuous (autocorr (pairProfile lam ρ₀)) := by
  unfold autocorr
  exact BddAbove.continuous_convolution_right_of_integrable L (reflect_pairProfile_bddAbove hlam ρ₀)
    (pairProfile_integrable hlam ρ₀) (reflect_continuous (pairProfile_continuous lam ρ₀))

/-! ## The line profile of the autocorrelation is integrable -/

/-- The weighted convolution is the convolution of the weighted factors. -/
theorem conv_mul_exp (f g : ℝ → ℂ) (s : ℂ) (x : ℝ) :
    (f ⋆[L] g) x * Complex.exp ((s - 1 / 2) * x)
      = ((fun y : ℝ => f y * Complex.exp ((s - 1 / 2) * y)) ⋆[L]
          (fun y : ℝ => g y * Complex.exp ((s - 1 / 2) * y))) x := by
  simp only [convolution_def, ContinuousLinearMap.mul_apply']
  rw [← integral_mul_const]
  congr 1
  funext t
  have hsplit : Complex.exp ((s - 1 / 2) * x) = Complex.exp ((s - 1 / 2) * t) * Complex.exp ((s - 1 / 2) * ((x - t : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [hsplit]; ring

theorem lineProfile_eq (g : ℝ → ℂ) (σ : ℝ) :
    lineProfile g σ = fun x : ℝ => g x * Complex.exp ((((σ : ℂ) - 1 / 2)) * x) := by
  funext x
  unfold lineProfile
  have hc : (((σ : ℂ) - 1 / 2)) * (x : ℂ) = (((σ - 1 / 2) * x : ℝ) : ℂ) := by push_cast; ring
  rw [hc, ← Complex.ofReal_exp]

theorem lineProfile_autocorr_integrable {lam : ℝ} (hlam : 0 < lam) (ρ₀ : ℂ) (σ : ℝ) :
    Integrable (lineProfile (autocorr (pairProfile lam ρ₀)) σ) := by
  rw [lineProfile_eq]
  have hfe := pairProfile_mul_exp_integrable hlam ρ₀ (σ : ℂ)
  have hge := reflect_pairProfile_mul_exp_integrable hlam ρ₀ (σ : ℂ)
  have hconv := Integrable.integrable_convolution L hfe hge
  refine hconv.congr ?_
  filter_upwards with x
  unfold autocorr
  exact (conv_mul_exp (pairProfile lam ρ₀) (reflect (pairProfile lam ρ₀)) (σ : ℂ) x).symm

/-! ## The transform is entire with Gaussian decay -/

theorem laplaceTest_autocorr_pairProfile_eq {lam : ℝ} (hlam : 0 < lam) (ρ₀ : ℂ) :
    laplaceTest (autocorr (pairProfile lam ρ₀))
      = fun s => -((Complex.normSq (gaussNorm lam) : ℂ) * pairDiff lam ρ₀ s ^ 2) :=
  funext fun s => pairProfile_autocorr_eq hlam ρ₀ s

theorem laplaceTest_autocorr_pairProfile_differentiable {lam : ℝ} (hlam : 0 < lam) (ρ₀ : ℂ) :
    Differentiable ℂ (laplaceTest (autocorr (pairProfile lam ρ₀))) := by
  rw [laplaceTest_autocorr_pairProfile_eq hlam]
  unfold pairDiff
  fun_prop

/-- `(1 + u²)² ≤ 4·exp(λu²)` for `λ ≥ 1`. -/
theorem one_add_sq_sq_le {lam : ℝ} (hlam : 1 ≤ lam) (u : ℝ) : (1 + u ^ 2) ^ 2 ≤ 4 * Real.exp (lam * u ^ 2) := by
  have h1 : 1 + u ^ 2 ≤ 2 * Real.exp (lam * u ^ 2 / 2) := by
    have := Real.add_one_le_exp (lam * u ^ 2 / 2)
    nlinarith [sq_nonneg u, mul_le_mul_of_nonneg_right hlam (sq_nonneg u)]
  have h0 : 0 ≤ 1 + u ^ 2 := by positivity
  have h2 : (1 + u ^ 2) ^ 2 ≤ (2 * Real.exp (lam * u ^ 2 / 2)) ^ 2 := pow_le_pow_left₀ h0 h1 2
  have h3 : (2 * Real.exp (lam * u ^ 2 / 2)) ^ 2 = 4 * Real.exp (lam * u ^ 2) := by
    rw [mul_pow, sq (Real.exp _), ← Real.exp_add]
    have : lam * u ^ 2 / 2 + lam * u ^ 2 / 2 = lam * u ^ 2 := by ring
    rw [this]; norm_num
  linarith

/-- `(1 + |T|)⁴ ≤ 64(1 + γ²)²·exp(λ(T − γ)²)` for `λ ≥ 1`. -/
theorem one_add_abs_pow_four_le {lam : ℝ} (hlam : 1 ≤ lam) (γ T : ℝ) :
    (1 + |T|) ^ 4 ≤ 64 * (1 + γ ^ 2) ^ 2 * Real.exp (lam * (T - γ) ^ 2) := by
  have hA : (1 + |T|) ^ 4 ≤ 4 * (1 + T ^ 2) ^ 2 := by
    have h1 : (1 + |T|) ^ 2 ≤ 2 * (1 + T ^ 2) := by nlinarith [sq_abs T, abs_nonneg T, sq_nonneg (|T| - 1)]
    have h0 : 0 ≤ (1 + |T|) ^ 2 := by positivity
    calc (1 + |T|) ^ 4 = ((1 + |T|) ^ 2) ^ 2 := by ring
      _ ≤ (2 * (1 + T ^ 2)) ^ 2 := pow_le_pow_left₀ h0 h1 2
      _ = 4 * (1 + T ^ 2) ^ 2 := by ring
  have hB : 1 + T ^ 2 ≤ 2 * (1 + γ ^ 2) * (1 + (T - γ) ^ 2) := by
    nlinarith [sq_nonneg (T - γ), sq_nonneg γ, sq_nonneg (T - 2 * γ), mul_nonneg (sq_nonneg γ) (sq_nonneg (T - γ))]
  have hB2 : (1 + T ^ 2) ^ 2 ≤ (2 * (1 + γ ^ 2) * (1 + (T - γ) ^ 2)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hB 2
  have hC := one_add_sq_sq_le hlam (T - γ)
  have hpos : 0 ≤ 4 * (1 + γ ^ 2) ^ 2 := by positivity
  calc (1 + |T|) ^ 4 ≤ 4 * (1 + T ^ 2) ^ 2 := hA
    _ ≤ 4 * (2 * (1 + γ ^ 2) * (1 + (T - γ) ^ 2)) ^ 2 := by linarith
    _ = 16 * (1 + γ ^ 2) ^ 2 * (1 + (T - γ) ^ 2) ^ 2 := by ring
    _ ≤ 16 * (1 + γ ^ 2) ^ 2 * (4 * Real.exp (lam * (T - γ) ^ 2)) := by
        apply mul_le_mul_of_nonneg_left hC; positivity
    _ = 64 * (1 + γ ^ 2) ^ 2 * Real.exp (lam * (T - γ) ^ 2) := by ring

/-- On a strip `[a, b]`, `‖D(x + iT)‖ ≤ 2·exp(λ(A − (T − γ)²))` with `A = (max |a| |b| + 1)²`. -/
theorem pairDiff_norm_le_strip {lam : ℝ} (hlam : 0 ≤ lam) {ρ₀ : ℂ} (hρ0 : 0 ≤ ρ₀.re) (hρ1 : ρ₀.re ≤ 1)
    {a b x T : ℝ} (hx : x ∈ Set.Icc a b) :
    ‖pairDiff lam ρ₀ (x + T * I)‖
      ≤ 2 * Real.exp (lam * ((max |a| |b| + 1) ^ 2 - (T - ρ₀.im) ^ 2)) := by
  have hM := pairDiff_norm_le_M hlam ρ₀ (x + T * I)
  refine hM.trans ?_
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ hlam
  unfold Mexp
  have hre : (↑x + ↑T * I : ℂ).re = x := by simp
  have him : (↑x + ↑T * I : ℂ).im = T := by simp
  rw [hre, him]
  have hxabs : |x| ≤ max |a| |b| := by
    rcases hx with ⟨hxa, hxb⟩
    rw [abs_le]; constructor
    · have := le_max_left |a| |b|; have := neg_abs_le a; linarith
    · have := le_max_right |a| |b|; have := le_abs_self b; linarith
  have hm0 : 0 ≤ max |a| |b| := le_trans (abs_nonneg a) (le_max_left _ _)
  have h1 : (x - ρ₀.re) ^ 2 ≤ (max |a| |b| + 1) ^ 2 := by
    have : |x - ρ₀.re| ≤ max |a| |b| + 1 := by
      calc |x - ρ₀.re| ≤ |x| + |ρ₀.re| := abs_sub _ _
        _ ≤ max |a| |b| + 1 := by rw [abs_of_nonneg hρ0]; linarith
    nlinarith [abs_nonneg (x - ρ₀.re), sq_abs (x - ρ₀.re)]
  have h2 : (x - (1 - ρ₀.re)) ^ 2 ≤ (max |a| |b| + 1) ^ 2 := by
    have : |x - (1 - ρ₀.re)| ≤ max |a| |b| + 1 := by
      calc |x - (1 - ρ₀.re)| ≤ |x| + |1 - ρ₀.re| := abs_sub _ _
        _ ≤ max |a| |b| + 1 := by
          rw [abs_of_nonneg (show (0 : ℝ) ≤ 1 - ρ₀.re by linarith)]; linarith
    nlinarith [abs_nonneg (x - (1 - ρ₀.re)), sq_abs (x - (1 - ρ₀.re))]
  have hmax : max ((x - ρ₀.re) ^ 2) ((x - (1 - ρ₀.re)) ^ 2) ≤ (max |a| |b| + 1) ^ 2 := max_le h1 h2
  linarith

/-- **Decay of order 4 on the strip** for the pair profile's transform. -/
theorem laplaceTest_autocorr_pairProfile_decay {lam : ℝ} (hlam : 1 ≤ lam) {ρ₀ : ℂ} (hρ0 : 0 ≤ ρ₀.re)
    (hρ1 : ρ₀.re ≤ 1) (a b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Set.Icc a b, ∀ T : ℝ,
      ‖laplaceTest (autocorr (pairProfile lam ρ₀)) (x + T * I)‖ ≤ C / (1 + |T|) ^ 4 := by
  set A : ℝ := (max |a| |b| + 1) ^ 2 with hA
  refine ⟨Complex.normSq (gaussNorm lam) * (4 * Real.exp (2 * lam * A)) * (64 * (1 + ρ₀.im ^ 2) ^ 2),
    mul_nonneg (mul_nonneg (Complex.normSq_nonneg _) (by positivity)) (by positivity), ?_⟩
  intro x hx T
  rw [laplaceTest_autocorr_pairProfile_eq (by linarith)]
  simp only [norm_neg, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Complex.normSq_nonneg _)]
  have hD := pairDiff_norm_le_strip (by linarith) hρ0 hρ1 hx (lam := lam) (T := T)
  have hD2 : ‖pairDiff lam ρ₀ (x + T * I)‖ ^ 2 ≤ 4 * Real.exp (2 * lam * A) * Real.exp (-(2 * lam) * (T - ρ₀.im) ^ 2) := by
    calc ‖pairDiff lam ρ₀ (x + T * I)‖ ^ 2
        ≤ (2 * Real.exp (lam * (A - (T - ρ₀.im) ^ 2))) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hD 2
      _ = 4 * Real.exp (2 * lam * A) * Real.exp (-(2 * lam) * (T - ρ₀.im) ^ 2) := by
          rw [mul_pow, sq (Real.exp _), ← Real.exp_add, mul_assoc, ← Real.exp_add]
          have : lam * (A - (T - ρ₀.im) ^ 2) + lam * (A - (T - ρ₀.im) ^ 2)
              = 2 * lam * A + -(2 * lam) * (T - ρ₀.im) ^ 2 := by ring
          rw [this]; norm_num
  have hpow := one_add_abs_pow_four_le hlam ρ₀.im T
  have hpos4 : 0 < (1 + |T|) ^ 4 := by positivity
  have hexp : Real.exp (-(2 * lam) * (T - ρ₀.im) ^ 2) ≤ 64 * (1 + ρ₀.im ^ 2) ^ 2 / (1 + |T|) ^ 4 := by
    rw [le_div_iff₀ hpos4]
    have hl2 : 1 ≤ 2 * lam := by linarith
    have hmono : Real.exp (lam * (T - ρ₀.im) ^ 2) ≤ Real.exp (2 * lam * (T - ρ₀.im) ^ 2) := by
      apply Real.exp_le_exp.mpr; nlinarith [sq_nonneg (T - ρ₀.im)]
    have hprod : Real.exp (-(2 * lam) * (T - ρ₀.im) ^ 2) * Real.exp (2 * lam * (T - ρ₀.im) ^ 2) = 1 := by
      rw [← Real.exp_add]; ring_nf; simp
    have hge : 0 ≤ Real.exp (-(2 * lam) * (T - ρ₀.im) ^ 2) := Real.exp_nonneg _
    calc Real.exp (-(2 * lam) * (T - ρ₀.im) ^ 2) * (1 + |T|) ^ 4
        ≤ Real.exp (-(2 * lam) * (T - ρ₀.im) ^ 2) * (64 * (1 + ρ₀.im ^ 2) ^ 2 * Real.exp (lam * (T - ρ₀.im) ^ 2)) :=
          mul_le_mul_of_nonneg_left hpow hge
      _ ≤ Real.exp (-(2 * lam) * (T - ρ₀.im) ^ 2) * (64 * (1 + ρ₀.im ^ 2) ^ 2 * Real.exp (2 * lam * (T - ρ₀.im) ^ 2)) := by
          apply mul_le_mul_of_nonneg_left _ hge
          apply mul_le_mul_of_nonneg_left hmono; positivity
      _ = 64 * (1 + ρ₀.im ^ 2) ^ 2 * (Real.exp (-(2 * lam) * (T - ρ₀.im) ^ 2) * Real.exp (2 * lam * (T - ρ₀.im) ^ 2)) := by ring
      _ = 64 * (1 + ρ₀.im ^ 2) ^ 2 := by rw [hprod, mul_one]
  rw [div_eq_mul_one_div]
  have hN : 0 ≤ Complex.normSq (gaussNorm lam) := Complex.normSq_nonneg _
  calc Complex.normSq (gaussNorm lam) * ‖pairDiff lam ρ₀ (x + T * I)‖ ^ 2
      ≤ Complex.normSq (gaussNorm lam) * (4 * Real.exp (2 * lam * A) * Real.exp (-(2 * lam) * (T - ρ₀.im) ^ 2)) :=
        mul_le_mul_of_nonneg_left hD2 hN
    _ ≤ Complex.normSq (gaussNorm lam) * (4 * Real.exp (2 * lam * A) * (64 * (1 + ρ₀.im ^ 2) ^ 2 / (1 + |T|) ^ 4)) := by
        apply mul_le_mul_of_nonneg_left _ hN
        apply mul_le_mul_of_nonneg_left hexp; positivity
    _ = Complex.normSq (gaussNorm lam) * (4 * Real.exp (2 * lam * A)) * (64 * (1 + ρ₀.im ^ 2) ^ 2) * (1 / (1 + |T|) ^ 4) := by
        ring

/-! ## The explicit formula at the pair profile, and the door -/

/-- **The explicit formula at the pair profile**: carrier side = zero side. -/
theorem carrierSide_pair_eq_zeroSide {lam : ℝ} (hlam : 1 ≤ lam) {ρ₀ : ℂ} (hρ0 : 0 ≤ ρ₀.re) (hρ1 : ρ₀.re ≤ 1)
    {a b : ℝ} (ha : a < 0) (hb : 1 < b) :
    carrierSide (autocorr (pairProfile lam ρ₀)) a b = zeroSide (autocorr (pairProfile lam ρ₀)) := by
  obtain ⟨C, hC, hdec⟩ := laplaceTest_autocorr_pairProfile_decay hlam hρ0 hρ1 a b
  exact (weil_explicit_formula' (autocorr_pairProfile_continuous (by linarith) ρ₀)
    (lineProfile_autocorr_integrable (by linarith) ρ₀ a) (lineProfile_autocorr_integrable (by linarith) ρ₀ b)
    (laplaceTest_autocorr_pairProfile_differentiable (by linarith) ρ₀) (le_refl 4) hC ha hb hdec).symm

/-- **Carrier positivity on the pair profiles**: the prime–Γ functional is nonnegative on the autocorrelation of
every pair profile with `λ ≥ 1` and centre in the strip. -/
def CarrierPositivePair (a b : ℝ) : Prop :=
  ∀ lam : ℝ, 1 ≤ lam → ∀ ρ₀ : ℂ, 0 ≤ ρ₀.re → ρ₀.re ≤ 1 →
    0 ≤ (carrierSide (autocorr (pairProfile lam ρ₀)) a b).re

/-- **Case B, stated**: if there is an off-axis zero, there is one of maximal deviation among the zeros within
height distance `2` of itself. -/
def LocalMaxExists : Prop :=
  (∃ ρ : Zero, ρ.val.re ≠ 1 / 2) →
    ∃ ρ₀ : Zero, ρ₀.val.re ≠ 1 / 2 ∧
      ∀ ρ : Zero, |ρ.val.im - ρ₀.val.im| < 2 → |ρ.val.re - 1 / 2| ≤ |ρ₀.val.re - 1 / 2|

/-- **The Gaussian-class door**: carrier positivity on the pair profiles and Case B put every zero on the axis. -/
theorem axis_of_carrierPositivePair {a b : ℝ} (ha : a < 0) (hb : 1 < b) (hpos : CarrierPositivePair a b)
    (hB : LocalMaxExists) : ∀ ρ ∈ ZD.NontrivialZeros, ρ.re = 1 / 2 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨ρ, hρ, hne⟩ := hcon
  obtain ⟨ρ₀, hβ, hmax⟩ := hB ⟨⟨ρ, hρ⟩, hne⟩
  obtain ⟨lam, hlam, hneg⟩ := gaussianWitness_of_locallyMax ρ₀ hβ hmax
  have hρ0 : 0 ≤ ρ₀.val.re := ρ₀.2.1.le
  have hρ1 : ρ₀.val.re ≤ 1 := ρ₀.2.2.1.le
  have hge := hpos lam hlam ρ₀.val hρ0 hρ1
  rw [carrierSide_pair_eq_zeroSide hlam hρ0 hρ1 ha hb] at hge
  unfold zeroSide at hge
  linarith

theorem riemannHypothesis_of_carrierPositivePair {a b : ℝ} (ha : a < 0) (hb : 1 < b)
    (hpos : CarrierPositivePair a b) (hB : LocalMaxExists) : RiemannHypothesis :=
  RHBridge.no_offline_zeros_implies_rh (axis_of_carrierPositivePair ha hb hpos hB)

end CriticalLinePhasor.HelixWeilWitness

end

#print axioms CriticalLinePhasor.HelixWeilWitness.carrierSide_pair_eq_zeroSide
#print axioms CriticalLinePhasor.HelixWeilWitness.riemannHypothesis_of_carrierPositivePair
