import RequestProject.HelixCarrierWeilDoor

/-!
# The Weil witness, brick W1: the Gaussian pair profile and its pair term (ledger 1336)

Toward `WeilWitness` (1335): for an off-axis zero `ρ₀ = β + iγ`, a test profile whose autocorrelation has
negative zero side. The profile built here is the DIFFERENCE of the two Gaussians centred at the pair
`(ρ₀, ρ₀* = 1 − ρ̄₀)` — the pair's two members, the J-image of each other:

  `pairProfile λ ρ₀ (x) = exp(b x² + (½ − ρ₀)x) − exp(b x² + (½ − ρ₀*)x)`,  `b = −1/(4λ)`.

* `laplaceTest_gaussProfile`: `∫ exp(b x² + (½−ρ)x) e^{(z−½)x} dx = N(λ)·exp(λ(z − ρ)²)` (Mathlib
  `integral_cexp_quadratic`), `N(λ) = (π/−b)^{1/2} ≠ 0`.
* `laplaceTest_pairProfile`: `H(z) = N(λ)·[exp(λ(z−ρ₀)²) − exp(λ(z−ρ₀*)²)]`.
* `laplaceTest_convolution_of_integrable`: the product law for the transform of a convolution, under integrability
  of the weighted profiles only (the compact-support version is `laplaceTest_convolution`, 1335).
* `pairProfile_autocorr_at_zero`: at `ρ₀` the autocorrelation's transform is `−|N|²·(E − 1)²`, `E = exp(λ(2β−1)²)`;
  `pairProfile_pair_term_neg`: it is strictly negative for every off-axis `ρ₀` and every `λ > 0`.

Mechanism: at `ρ₀` the two Gaussians read `1 − E` and `E − 1` — the pair's own value `E = exp(λ(2β−1)²)` with the
sign flipped between the two ends — so the product is `−(E−1)²`, and it grows like `exp(8λ(β−½)²)`, faster than any
axis term (`|H|² ≤ 4|N|² exp(2λ(β−½)²)`). What remains for `WeilWitness`: the dominance over the whole zero sum
(W2) and the truncation to compact support (W3). No `sorry`, no `axiom`, no window.
-/

open Complex MeasureTheory
open scoped Real ComplexConjugate Convolution

noncomputable section

namespace CriticalLinePhasor.HelixWeilWitness

open CriticalLinePhasor.ContourArgument CriticalLinePhasor.HelixCarrierWeil

/-- The quadratic coefficient `b = −1/(4λ)`. -/
def bcoef (lam : ℝ) : ℂ := ((-(1 / (4 * lam)) : ℝ) : ℂ)

theorem bcoef_re_neg {lam : ℝ} (hlam : 0 < lam) : (bcoef lam).re < 0 := by
  unfold bcoef
  rw [Complex.ofReal_re]
  have : 0 < 1 / (4 * lam) := by positivity
  linarith

theorem bcoef_eq (lam : ℝ) : bcoef lam = -(1 / (4 * (lam : ℂ))) := by
  unfold bcoef; push_cast; ring

/-- The Gaussian profile centred at `ρ`: `exp(b x² + (½ − ρ)x)`. -/
def gaussProfile (lam : ℝ) (ρ : ℂ) (x : ℝ) : ℂ :=
  Complex.exp (bcoef lam * (x : ℂ) ^ 2 + (1 / 2 - ρ) * x)

/-- The Gaussian normalisation `N(λ) = (π/−b)^{1/2}`. -/
def gaussNorm (lam : ℝ) : ℂ := ((π : ℂ) / -(bcoef lam)) ^ (1 / 2 : ℂ)

theorem gaussNorm_ne_zero {lam : ℝ} (hlam : 0 < lam) : gaussNorm lam ≠ 0 := by
  unfold gaussNorm
  intro h
  rw [Complex.cpow_eq_zero_iff] at h
  have hbase : (π : ℂ) / -(bcoef lam) ≠ 0 := by
    rw [bcoef_eq]
    have hl : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam.ne'
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp
    exact mul_ne_zero (mul_ne_zero hπ (by norm_num)) hl
  exact hbase h.1

/-- The weighted Gaussian is integrable. -/
theorem gaussProfile_mul_exp_integrable {lam : ℝ} (hlam : 0 < lam) (ρ z : ℂ) :
    Integrable (fun x : ℝ => gaussProfile lam ρ x * Complex.exp ((z - 1 / 2) * x)) := by
  have h := integrable_cexp_quadratic' (bcoef_re_neg hlam) (z - ρ) 0
  refine h.congr ?_
  filter_upwards with x
  unfold gaussProfile
  rw [← Complex.exp_add]
  congr 1
  ring

/-- **The Gaussian transform**: `laplaceTest (gaussProfile λ ρ) z = N(λ)·exp(λ(z − ρ)²)`. -/
theorem laplaceTest_gaussProfile {lam : ℝ} (hlam : 0 < lam) (ρ z : ℂ) :
    laplaceTest (gaussProfile lam ρ) z = gaussNorm lam * Complex.exp (lam * (z - ρ) ^ 2) := by
  unfold laplaceTest gaussProfile gaussNorm
  have hpt : ∀ x : ℝ, Complex.exp (bcoef lam * (x : ℂ) ^ 2 + (1 / 2 - ρ) * x) * Complex.exp ((z - 1 / 2) * x)
      = Complex.exp (bcoef lam * (x : ℂ) ^ 2 + (z - ρ) * x + 0) := by
    intro x
    rw [← Complex.exp_add]
    congr 1
    ring
  simp_rw [hpt]
  rw [integral_cexp_quadratic (bcoef_re_neg hlam) (z - ρ) 0]
  congr 1
  rw [bcoef_eq]
  have hl : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam.ne'
  congr 1
  field_simp
  ring

/-- The pair profile: the difference of the Gaussians at `ρ₀` and at its mirror `ρ₀* = 1 − ρ̄₀`. -/
def pairProfile (lam : ℝ) (ρ₀ : ℂ) (x : ℝ) : ℂ :=
  gaussProfile lam ρ₀ x - gaussProfile lam (1 - conj ρ₀) x

theorem pairProfile_mul_exp_integrable {lam : ℝ} (hlam : 0 < lam) (ρ₀ z : ℂ) :
    Integrable (fun x : ℝ => pairProfile lam ρ₀ x * Complex.exp ((z - 1 / 2) * x)) := by
  have h := (gaussProfile_mul_exp_integrable hlam ρ₀ z).sub (gaussProfile_mul_exp_integrable hlam (1 - conj ρ₀) z)
  refine h.congr ?_
  filter_upwards with x
  simp only [Pi.sub_apply]
  unfold pairProfile
  ring

/-- **The pair profile's transform**: `H(z) = N(λ)·[exp(λ(z−ρ₀)²) − exp(λ(z−ρ₀*)²)]`. -/
theorem laplaceTest_pairProfile {lam : ℝ} (hlam : 0 < lam) (ρ₀ z : ℂ) :
    laplaceTest (pairProfile lam ρ₀) z
      = gaussNorm lam * (Complex.exp (lam * (z - ρ₀) ^ 2) - Complex.exp (lam * (z - (1 - conj ρ₀)) ^ 2)) := by
  have h1 := laplaceTest_gaussProfile hlam ρ₀ z
  have h2 := laplaceTest_gaussProfile hlam (1 - conj ρ₀) z
  unfold laplaceTest at h1 h2 ⊢
  have hsplit : (fun x : ℝ => pairProfile lam ρ₀ x * Complex.exp ((z - 1 / 2) * x))
      = fun x : ℝ => gaussProfile lam ρ₀ x * Complex.exp ((z - 1 / 2) * x)
        - gaussProfile lam (1 - conj ρ₀) x * Complex.exp ((z - 1 / 2) * x) := by
    funext x; unfold pairProfile; ring
  rw [hsplit, integral_sub (gaussProfile_mul_exp_integrable hlam ρ₀ z)
    (gaussProfile_mul_exp_integrable hlam (1 - conj ρ₀) z), h1, h2]
  ring

/-! ## The product law under integrability only -/

theorem laplaceTest_convolution_of_integrable {f g : ℝ → ℂ} (s : ℂ)
    (hfe : Integrable (fun x : ℝ => f x * Complex.exp ((s - 1 / 2) * x)))
    (hge : Integrable (fun x : ℝ => g x * Complex.exp ((s - 1 / 2) * x))) :
    laplaceTest (f ⋆[L] g) s = laplaceTest f s * laplaceTest g s := by
  set e : ℝ → ℂ := fun x => Complex.exp ((s - 1 / 2) * x) with he
  have hsplit : ∀ x t : ℝ, e x = e t * e (x - t) := by
    intro x t
    simp only [he]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hconv : ∀ x : ℝ, (f ⋆[L] g) x * e x = ((f * e) ⋆[L] (g * e)) x := by
    intro x
    simp only [convolution_def, ContinuousLinearMap.mul_apply', Pi.mul_apply]
    rw [← integral_mul_const]
    congr 1
    funext t
    rw [hsplit x t]
    ring
  have h1 : laplaceTest (f ⋆[L] g) s = ∫ x : ℝ, ((f * e) ⋆[L] (g * e)) x := by
    unfold laplaceTest
    congr 1
    funext x
    exact hconv x
  have hfe' : Integrable (f * e) := hfe
  have hge' : Integrable (g * e) := hge
  rw [h1, integral_convolution L hfe' hge', ContinuousLinearMap.mul_apply']
  rfl

/-- The reflected pair profile's weighted form is integrable. -/
theorem reflect_pairProfile_mul_exp_integrable {lam : ℝ} (hlam : 0 < lam) (ρ₀ z : ℂ) :
    Integrable (fun x : ℝ => reflect (pairProfile lam ρ₀) x * Complex.exp ((z - 1 / 2) * x)) := by
  -- reflect (pairProfile) = pairProfile at the conjugate-mirror centres, up to the sign of `x`
  have hG : ∀ ρ : ℂ, ∀ x : ℝ, conj (gaussProfile lam ρ (-x)) = gaussProfile lam (1 - conj ρ) x := by
    intro ρ x
    unfold gaussProfile
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_add, map_mul, map_sub, map_neg, map_pow, Complex.conj_ofReal, map_div₀, map_one, map_ofNat,
      Complex.ofReal_neg, bcoef]
    ring
  have hre : ∀ x : ℝ, reflect (pairProfile lam ρ₀) x
      = gaussProfile lam (1 - conj ρ₀) x - gaussProfile lam ρ₀ x := by
    intro x
    unfold reflect pairProfile
    rw [map_sub, hG, hG, map_sub, map_one, Complex.conj_conj, sub_sub_cancel]
  have h := (gaussProfile_mul_exp_integrable hlam (1 - conj ρ₀) z).sub (gaussProfile_mul_exp_integrable hlam ρ₀ z)
  refine h.congr ?_
  filter_upwards with x
  simp only [Pi.sub_apply]
  rw [hre x]
  ring

/-- **The autocorrelation's transform at `ρ₀`**: `−|N|²·(E − 1)²`, `E = exp(λ(2β − 1)²)`. -/
theorem pairProfile_autocorr_at_zero {lam : ℝ} (hlam : 0 < lam) (ρ₀ : ℂ) :
    laplaceTest (autocorr (pairProfile lam ρ₀)) ρ₀
      = -((Complex.normSq (gaussNorm lam) : ℂ)
          * ((Complex.exp (lam * ((2 * ρ₀.re - 1 : ℝ) : ℂ) ^ 2) - 1) ^ 2)) := by
  unfold autocorr
  rw [laplaceTest_convolution_of_integrable ρ₀ (pairProfile_mul_exp_integrable hlam ρ₀ ρ₀)
    (reflect_pairProfile_mul_exp_integrable hlam ρ₀ ρ₀), laplaceTest_reflect,
    laplaceTest_pairProfile hlam, laplaceTest_pairProfile hlam]
  -- the two Gaussian values at the pair
  have hd : ρ₀ - (1 - conj ρ₀) = ((2 * ρ₀.re - 1 : ℝ) : ℂ) := by
    apply Complex.ext
    · simp [Complex.conj_re]; ring
    · simp [Complex.conj_im]
  have hd' : (1 - conj ρ₀) - ρ₀ = -((2 * ρ₀.re - 1 : ℝ) : ℂ) := by
    rw [← hd]; ring
  set E : ℂ := Complex.exp (lam * ((2 * ρ₀.re - 1 : ℝ) : ℂ) ^ 2) with hE
  have hEreal : conj E = E := by
    rw [hE, ← Complex.exp_conj]
    congr 1
    simp only [map_mul, map_pow, Complex.conj_ofReal]
  have h1 : Complex.exp (lam * (ρ₀ - ρ₀) ^ 2) = 1 := by simp
  have h2 : Complex.exp (lam * (ρ₀ - (1 - conj ρ₀)) ^ 2) = E := by rw [hd]
  have h3 : Complex.exp (lam * ((1 - conj ρ₀) - ρ₀) ^ 2) = E := by rw [hd', neg_sq]
  have h4 : Complex.exp (lam * ((1 - conj ρ₀) - (1 - conj ρ₀)) ^ 2) = 1 := by simp
  rw [h1, h2, h3, h4, map_mul, map_sub, hEreal, map_one, ← Complex.mul_conj]
  ring

/-- **The pair term is strictly negative** for every off-axis `ρ₀` and every `λ > 0`. -/
theorem pairProfile_pair_term_neg {lam : ℝ} (hlam : 0 < lam) {ρ₀ : ℂ} (hρ : ρ₀.re ≠ 1 / 2) :
    (laplaceTest (autocorr (pairProfile lam ρ₀)) ρ₀).re < 0 := by
  rw [pairProfile_autocorr_at_zero hlam]
  have hE : Complex.exp (lam * ((2 * ρ₀.re - 1 : ℝ) : ℂ) ^ 2) = ((Real.exp (lam * (2 * ρ₀.re - 1) ^ 2) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp]; push_cast; ring_nf
  rw [hE]
  have hN : 0 < Complex.normSq (gaussNorm lam) := Complex.normSq_pos.mpr (gaussNorm_ne_zero hlam)
  have hpos : 0 < lam * (2 * ρ₀.re - 1) ^ 2 := by
    have : 2 * ρ₀.re - 1 ≠ 0 := by intro h; apply hρ; linarith
    positivity
  have hE1 : Real.exp (lam * (2 * ρ₀.re - 1) ^ 2) - 1 > 0 := by
    have := Real.one_lt_exp_iff.mpr hpos
    linarith
  have hsq : 0 < (Real.exp (lam * (2 * ρ₀.re - 1) ^ 2) - 1) ^ 2 := by positivity
  have hcast : -((Complex.normSq (gaussNorm lam) : ℂ)
      * ((((Real.exp (lam * (2 * ρ₀.re - 1) ^ 2) : ℝ) : ℂ) - 1) ^ 2))
      = (((-(Complex.normSq (gaussNorm lam) * (Real.exp (lam * (2 * ρ₀.re - 1) ^ 2) - 1) ^ 2)) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hcast, Complex.ofReal_re]
  nlinarith [mul_pos hN hsq]

/-! ## W1b — the whole zero side in one shape: `F(z) = −|N|²·D(z)²` -/

/-- The pair difference `D(z) = e^{λ(z−ρ₀)²} − e^{λ(z−ρ₀*)²}`. -/
def pairDiff (lam : ℝ) (ρ₀ z : ℂ) : ℂ :=
  Complex.exp (lam * (z - ρ₀) ^ 2) - Complex.exp (lam * (z - (1 - conj ρ₀)) ^ 2)

/-- The mirror identity: `conj H(1 − z̄) = −conj N · D(z)`. -/
theorem conj_laplaceTest_pairProfile_mirror {lam : ℝ} (hlam : 0 < lam) (ρ₀ z : ℂ) :
    conj (laplaceTest (pairProfile lam ρ₀) (1 - conj z)) = -(conj (gaussNorm lam)) * pairDiff lam ρ₀ z := by
  rw [laplaceTest_pairProfile hlam, map_mul, map_sub, ← Complex.exp_conj, ← Complex.exp_conj]
  have e1 : conj ((lam : ℂ) * ((1 - conj z) - ρ₀) ^ 2) = lam * (z - (1 - conj ρ₀)) ^ 2 := by
    simp only [map_mul, map_pow, map_sub, map_one, Complex.conj_conj, Complex.conj_ofReal]
    ring
  have e2 : conj ((lam : ℂ) * ((1 - conj z) - (1 - conj ρ₀)) ^ 2) = lam * (z - ρ₀) ^ 2 := by
    simp only [map_mul, map_pow, map_sub, map_one, Complex.conj_conj, Complex.conj_ofReal]
    ring
  rw [e1, e2]
  unfold pairDiff
  ring

/-- **The zero side's shape**: `laplaceTest (autocorr (pairProfile λ ρ₀)) z = −|N|²·D(z)²` for every `z`. -/
theorem pairProfile_autocorr_eq {lam : ℝ} (hlam : 0 < lam) (ρ₀ z : ℂ) :
    laplaceTest (autocorr (pairProfile lam ρ₀)) z
      = -((Complex.normSq (gaussNorm lam) : ℂ) * pairDiff lam ρ₀ z ^ 2) := by
  unfold autocorr
  rw [laplaceTest_convolution_of_integrable z (pairProfile_mul_exp_integrable hlam ρ₀ z)
    (reflect_pairProfile_mul_exp_integrable hlam ρ₀ z), laplaceTest_reflect,
    conj_laplaceTest_pairProfile_mirror hlam, laplaceTest_pairProfile hlam]
  rw [← Complex.mul_conj]
  unfold pairDiff
  ring

/-- On the axis the pair difference is purely imaginary: `D(½+it) = −conj D(½+it)`. -/
theorem pairDiff_axis_conj (lam : ℝ) (ρ₀ : ℂ) {z : ℂ} (hz : z.re = 1 / 2) :
    conj (pairDiff lam ρ₀ z) = -pairDiff lam ρ₀ z := by
  have hmir : (1 : ℂ) - conj z = z := by
    apply Complex.ext
    · simp [Complex.conj_re]; linarith
    · simp [Complex.conj_im]
  have hcz : conj z = 1 - z := by linear_combination -hmir
  unfold pairDiff
  rw [map_sub, ← Complex.exp_conj, ← Complex.exp_conj]
  have e1 : conj ((lam : ℂ) * (z - ρ₀) ^ 2) = lam * (z - (1 - conj ρ₀)) ^ 2 := by
    simp only [map_mul, map_pow, map_sub, Complex.conj_ofReal]
    rw [hcz]
    ring
  have e2 : conj ((lam : ℂ) * (z - (1 - conj ρ₀)) ^ 2) = lam * (z - ρ₀) ^ 2 := by
    simp only [map_mul, map_pow, map_sub, map_one, Complex.conj_conj, Complex.conj_ofReal]
    rw [hcz]
    ring
  rw [e1, e2]
  ring

/-- **Axis terms are nonnegative**: on the axis `Re[−|N|² D²] = |N|²·|D|² ≥ 0`. -/
theorem pairProfile_autocorr_axis_nonneg {lam : ℝ} (hlam : 0 < lam) (ρ₀ : ℂ) {z : ℂ} (hz : z.re = 1 / 2) :
    0 ≤ (laplaceTest (autocorr (pairProfile lam ρ₀)) z).re := by
  rw [pairProfile_autocorr_eq hlam]
  have hD : pairDiff lam ρ₀ z ^ 2 = -((Complex.normSq (pairDiff lam ρ₀ z) : ℂ)) := by
    rw [← Complex.mul_conj, pairDiff_axis_conj lam ρ₀ hz]
    ring
  rw [hD]
  have : -((Complex.normSq (gaussNorm lam) : ℂ) * -((Complex.normSq (pairDiff lam ρ₀ z) : ℂ)))
      = (((Complex.normSq (gaussNorm lam) * Complex.normSq (pairDiff lam ρ₀ z)) : ℝ) : ℂ) := by
    push_cast; ring
  rw [this, Complex.ofReal_re]
  exact mul_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)

end CriticalLinePhasor.HelixWeilWitness

end

#print axioms CriticalLinePhasor.HelixWeilWitness.pairProfile_autocorr_eq
#print axioms CriticalLinePhasor.HelixWeilWitness.pairProfile_autocorr_axis_nonneg

#print axioms CriticalLinePhasor.HelixWeilWitness.laplaceTest_gaussProfile
#print axioms CriticalLinePhasor.HelixWeilWitness.laplaceTest_pairProfile
#print axioms CriticalLinePhasor.HelixWeilWitness.pairProfile_autocorr_at_zero
#print axioms CriticalLinePhasor.HelixWeilWitness.pairProfile_pair_term_neg
