import RequestProject.FrobeniusSimilitude

/-!
# Leafwise conformal purity (ledger 975; plan 974, steps C and A)

Sam, 2026-10-01: "why do we need to build on a square, the helix is an open curve, right?" — and, on the re-plan,
"lets go".

Deninger, *Arithmetic geometry and analysis on foliated spaces* (arXiv:math/0505354), Theorem 4.1: on a compact
3-manifold foliated by surfaces, a flow that is conformal on the leaves with factor `e^{αt}` has infinitesimal
generator `Θ = α/2 + S`, `S` skew, on reduced leafwise `H̄¹`; so every spectral value has real part `α/2`. No square
enters: the positivity is the `★`-inner product of a leafwise metric, `(h, h') = tr(h ∪ ★h')`.

## Step C — the algebra of Theorem 4.1, on any complex inner-product space

The inner product is assumed to be the `★`-pairing of a cup form `B`: `⟪h, h'⟫ = B h (★ h')`.

* `similitude_of_cup_conformal` (discrete, Frobenius form): if Frobenius acts on the cup form by `c`
  (`B (F h) (F h') = c · B h h'`, i.e. on `H²` by `c`) and commutes with `★` (conformality), then `F` is a similitude
  of the inner product with ratio `c`.
* `eigenvalue_normSq_of_similitude`: every eigenvalue of such an `F` has `|λ|² = c`.
* `re_eq_half_of_normSq_cpow`, `purity_of_cup_conformal`: for `c = p > 1` and eigenvalue `p^ρ`, `Re ρ = 1/2`.
* `generator_skew_of_cup_derivation`, `re_eq_of_generator_eigenvalue` (infinitesimal form): Theorem 4.1's
  computation `α(h ∪ h') = Θh ∪ h' + h ∪ Θh'` with `Θ★ = ★Θ` gives `⟪Θh, h'⟫ + ⟪h, Θh'⟫ = α⟪h, h'⟫`, hence
  `Re ρ = α/2` for every eigenvalue.

## Step A — the carrier leaf is conformal with `α = 1`

* `frobeniusSimilitude_hermitian`: the similitude scales the Hermitian metric of the carrier line by exactly `m`:
  `S z · conj (S w) = m · z · conj w` (both its real part, the Euclidean metric, and its imaginary part, the area form).
* `frobeniusSimilitude_det`: as an `ℝ`-linear map of the leaf `ℂ ≅ ℝ²` its determinant is `m` — Frobenius acts on the
  leaf's top form by the area-law factor, Deninger's `Θ = α` on `H̄²`.
* `conformalFlow`, `conformalFlow_hermitian`: the flow `z ↦ e^{t(1/2 + iκ)} z` scales the metric by `e^t` (`α = 1`)
  for every rotation rate `κ`; `norm_frobeniusMultiplier_eq_flow`: at time `t = log m` its ratio is the similitude's
  `√m`.

No hypothesis in this file concerns `ζ` or its zeros. What the file does NOT supply is plan 974's step B: a leafwise
cohomology whose `Θ`-spectrum is the zeros, with the flow conformal on it.
-/

open Complex

noncomputable section

namespace CriticalLinePhasor.LeafwiseConformalPurity

/-! ## Step C — the algebra of Deninger's Theorem 4.1 -/

section Algebra

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- **Conformal Frobenius is a similitude.** If the inner product is the `★`-pairing of the cup form `B`, Frobenius
acts on the cup form by `c`, and Frobenius commutes with `★`, then Frobenius scales the inner product by `c`. -/
theorem similitude_of_cup_conformal (B : E → E → ℂ) (star F : E → E) (c : ℂ)
    (hB : ∀ h h', inner ℂ h h' = B h (star h'))
    (hcup : ∀ h h', B (F h) (F h') = c * B h h')
    (hcomm : ∀ h, F (star h) = star (F h)) :
    ∀ h h', inner ℂ (F h) (F h') = c * inner ℂ h h' := by
  intro h h'
  rw [hB (F h) (F h'), ← hcomm h', hcup h (star h'), ← hB h h']

/-- **Eigenvalues of a similitude have modulus `√c`.** -/
theorem eigenvalue_normSq_of_similitude (F : E → E) (c : ℝ)
    (hsim : ∀ h h', inner ℂ (F h) (F h') = (c : ℂ) * inner ℂ h h')
    {v : E} (hv : v ≠ 0) {lam : ℂ} (hF : F v = lam • v) :
    Complex.normSq lam = c := by
  have h1 := hsim v v
  rw [hF, inner_smul_left, inner_smul_right] at h1
  have hvv : inner ℂ v v ≠ 0 := inner_self_ne_zero.mpr hv
  have h2 : (starRingEnd ℂ) lam * lam = (c : ℂ) := by
    apply mul_right_cancel₀ hvv
    rw [mul_assoc]
    exact h1
  have h3 : ((Complex.normSq lam : ℝ) : ℂ) = (c : ℂ) := by
    rw [Complex.normSq_eq_conj_mul_self]
    exact h2
  exact_mod_cast h3

/-- **Purity from the modulus.** If `|p^ρ|² = p` with `p > 1`, then `Re ρ = 1/2`. -/
theorem re_eq_half_of_normSq_cpow {p : ℝ} (hp : 1 < p) {ρ : ℂ}
    (h : Complex.normSq ((p : ℂ) ^ ρ) = p) : ρ.re = 1 / 2 := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hnorm : ‖(p : ℂ) ^ ρ‖ = p ^ ρ.re := Complex.norm_cpow_eq_rpow_re_of_pos hp0 ρ
  rw [Complex.normSq_eq_norm_sq, hnorm, ← Real.rpow_natCast, ← Real.rpow_mul hp0.le] at h
  have hlog := congrArg Real.log h
  rw [Real.log_rpow hp0] at hlog
  have hlogp : 0 < Real.log p := Real.log_pos hp
  have : ρ.re * (2 : ℕ) = 1 := by
    have := mul_right_cancel₀ hlogp.ne' (hlog.trans (one_mul _).symm)
    exact this
  push_cast at this
  linarith

/-- **Leafwise conformal purity, discrete form.** A Frobenius that acts on the cup form by `p > 1` and commutes with
the `★` defining the inner product has every eigenvalue of the form `p^ρ` on the line `Re ρ = 1/2`. -/
theorem purity_of_cup_conformal (B : E → E → ℂ) (star F : E → E) {p : ℝ} (hp : 1 < p)
    (hB : ∀ h h', inner ℂ h h' = B h (star h'))
    (hcup : ∀ h h', B (F h) (F h') = (p : ℂ) * B h h')
    (hcomm : ∀ h, F (star h) = star (F h))
    {v : E} (hv : v ≠ 0) {ρ : ℂ} (hF : F v = ((p : ℂ) ^ ρ) • v) : ρ.re = 1 / 2 :=
  re_eq_half_of_normSq_cpow hp
    (eigenvalue_normSq_of_similitude F p (similitude_of_cup_conformal B star F p hB hcup hcomm) hv hF)

/-- **Deninger's Theorem 4.1, the computation.** If the inner product is the `★`-pairing of the cup form, the
generator is a derivation of the cup form into `H²` with `Θ = α` there, and `Θ` commutes with `★`, then
`⟪Θh, h'⟫ + ⟪h, Θh'⟫ = α⟪h, h'⟫`: `Θ − α/2` is skew. -/
theorem generator_skew_of_cup_derivation (B : E → E → ℂ) (star Θ : E → E) (α : ℂ)
    (hB : ∀ h h', inner ℂ h h' = B h (star h'))
    (hcup : ∀ h h', B (Θ h) h' + B h (Θ h') = α * B h h')
    (hcomm : ∀ h, Θ (star h) = star (Θ h)) :
    ∀ h h', inner ℂ (Θ h) h' + inner ℂ h (Θ h') = α * inner ℂ h h' := by
  intro h h'
  rw [hB (Θ h) h', hB h (Θ h'), ← hcomm h', hcup h (star h'), ← hB h h']

/-- **Every eigenvalue of a generator with `Θ − α/2` skew has real part `α/2`.** -/
theorem re_eq_of_generator_eigenvalue (Θ : E → E) (α : ℝ)
    (hskew : ∀ h h', inner ℂ (Θ h) h' + inner ℂ h (Θ h') = (α : ℂ) * inner ℂ h h')
    {v : E} (hv : v ≠ 0) {ρ : ℂ} (hΘ : Θ v = ρ • v) : ρ.re = α / 2 := by
  have h1 := hskew v v
  rw [hΘ, inner_smul_left, inner_smul_right, ← add_mul] at h1
  have hvv : inner ℂ v v ≠ 0 := inner_self_ne_zero.mpr hv
  have h2 : (starRingEnd ℂ) ρ + ρ = (α : ℂ) := mul_right_cancel₀ hvv h1
  have h3 := congrArg Complex.re h2
  simp only [Complex.add_re, Complex.conj_re, Complex.ofReal_re] at h3
  linarith

/-- **Deninger's Theorem 4.1, packaged.** Cup derivation with `Θ = α` on `H²`, plus `Θ★ = ★Θ`, puts every eigenvalue
of `Θ` on `Re ρ = α/2`; at `α = 1` this is the line `1/2`. -/
theorem deninger_conformal_purity (B : E → E → ℂ) (star Θ : E → E) (α : ℝ)
    (hB : ∀ h h', inner ℂ h h' = B h (star h'))
    (hcup : ∀ h h', B (Θ h) h' + B h (Θ h') = (α : ℂ) * B h h')
    (hcomm : ∀ h, Θ (star h) = star (Θ h))
    {v : E} (hv : v ≠ 0) {ρ : ℂ} (hΘ : Θ v = ρ • v) : ρ.re = α / 2 :=
  re_eq_of_generator_eigenvalue Θ α (generator_skew_of_cup_derivation B star Θ α hB hcup hcomm) hv hΘ

end Algebra

/-! ## Step A — the carrier leaf is conformal with `α = 1` -/

/-- The multiplier times its conjugate is `m`: the similitude's squared ratio is the area-law factor. -/
theorem frobeniusMultiplier_mul_conj (θ : ℕ → ℝ) (m : ℕ) :
    FrobeniusSimilitude.frobeniusMultiplier θ m
      * (starRingEnd ℂ) (FrobeniusSimilitude.frobeniusMultiplier θ m) = (m : ℂ) := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, FrobeniusSimilitude.norm_frobeniusMultiplier,
    Real.sq_sqrt (Nat.cast_nonneg m)]
  simp

/-- **The carrier leaf is conformal.** The Frobenius similitude scales the Hermitian metric of the carrier line by
exactly `m` — its real part (the Euclidean metric) and its imaginary part (the area form) alike. -/
theorem frobeniusSimilitude_hermitian (θ : ℕ → ℝ) (m : ℕ) (z w : ℂ) :
    FrobeniusSimilitude.frobeniusSimilitude θ m z
        * (starRingEnd ℂ) (FrobeniusSimilitude.frobeniusSimilitude θ m w)
      = (m : ℂ) * (z * (starRingEnd ℂ) w) := by
  simp only [FrobeniusSimilitude.frobeniusSimilitude_apply, map_mul]
  rw [← frobeniusMultiplier_mul_conj θ m]
  ring

/-- **Frobenius acts on the leaf's top form by the area-law factor.** As an `ℝ`-linear map of the leaf `ℂ ≅ ℝ²`,
multiplication by the Frobenius multiplier has determinant `m`. -/
theorem frobeniusSimilitude_det (θ : ℕ → ℝ) (m : ℕ) :
    LinearMap.det (Algebra.lmul ℝ ℂ (FrobeniusSimilitude.frobeniusMultiplier θ m)) = (m : ℝ) := by
  rw [← Algebra.norm_apply, Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq,
    FrobeniusSimilitude.norm_frobeniusMultiplier, Real.sq_sqrt (Nat.cast_nonneg m)]

/-- The real part of the flow exponent `t(1/2 + iκ)` is `t/2`. -/
theorem flow_exponent_re (κ t : ℝ) : ((t : ℂ) * (1 / 2 + (κ : ℂ) * Complex.I)).re = t / 2 := by
  simp [Complex.mul_re]
  ring

/-- The conformal flow on the carrier line with rotation rate `κ`: `z ↦ e^{t(1/2 + iκ)} z`. -/
def conformalFlow (κ t : ℝ) (z : ℂ) : ℂ := Complex.exp ((t : ℂ) * (1 / 2 + (κ : ℂ) * Complex.I)) * z

/-- **The flow is conformal with exponent `α = 1`**: it scales the Hermitian metric by `e^t`, for every rotation rate. -/
theorem conformalFlow_hermitian (κ t : ℝ) (z w : ℂ) :
    conformalFlow κ t z * (starRingEnd ℂ) (conformalFlow κ t w)
      = (Real.exp t : ℂ) * (z * (starRingEnd ℂ) w) := by
  have hμ : Complex.exp ((t : ℂ) * (1 / 2 + (κ : ℂ) * Complex.I))
      * (starRingEnd ℂ) (Complex.exp ((t : ℂ) * (1 / 2 + (κ : ℂ) * Complex.I))) = (Real.exp t : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.norm_exp, flow_exponent_re,
      ← Real.exp_nat_mul]
    push_cast
    ring_nf
  simp only [conformalFlow, map_mul]
  rw [← hμ]
  ring

/-- **At time `log m` the flow's ratio is the similitude's `√m`.** -/
theorem norm_frobeniusMultiplier_eq_flow (θ : ℕ → ℝ) (κ : ℝ) {m : ℕ} (hm : m ≠ 0) :
    ‖FrobeniusSimilitude.frobeniusMultiplier θ m‖ = ‖conformalFlow κ (Real.log m) 1‖ := by
  rw [FrobeniusSimilitude.norm_frobeniusMultiplier, conformalFlow, mul_one, Complex.norm_exp,
    flow_exponent_re]
  have hm0 : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hm0]
  ring_nf

/-! ## Step B, first check — closed-orbit weights at the leaf origin

The similitude fixes the origin of the leaf, so a closed orbit of the flow passes through it. Its linearised return
map after time `k·log m` is `μ_m^k`. Deninger's leafwise trace formula (math/0505354, §7) weights such an orbit by
`ε = sign det(1 − Tφ)` at positive times and by `det(−Tφ)` at negative times. -/

/-- **Positive-time sign.** For `m ≥ 2` and `k ≥ 1`, `det_ℝ(1 − μ_m^k) > 0`. Every closed orbit through the leaf
origin carries `ε = +1`, the uniform sign of the prime side of the explicit formula. -/
theorem lefschetz_sign_pos (θ : ℕ → ℝ) {m : ℕ} (hm : 2 ≤ m) {k : ℕ} (hk : 1 ≤ k) :
    0 < LinearMap.det (Algebra.lmul ℝ ℂ (1 - FrobeniusSimilitude.frobeniusMultiplier θ m ^ k)) := by
  rw [← Algebra.norm_apply, Algebra.norm_complex_apply, Complex.normSq_pos, sub_ne_zero]
  intro h
  have hn : ‖FrobeniusSimilitude.frobeniusMultiplier θ m ^ k‖ = 1 := by
    rw [← h]
    simp
  rw [norm_pow, FrobeniusSimilitude.norm_frobeniusMultiplier] at hn
  have h1 : 1 < Real.sqrt m := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_lt_sqrt (by norm_num) (by exact_mod_cast (by omega : 1 < m))
  have h2 : 1 < Real.sqrt m ^ k := one_lt_pow₀ h1 (by omega)
  linarith

/-- **Negative-time weight.** `det_ℝ(−μ_m^k) = m^k`. Inverting the return map, Deninger's negative-time weight is
`m^{−k}`: the explicit formula's `p^{−k}`, supplied by the area law. -/
theorem lefschetz_weight_neg (θ : ℕ → ℝ) (m k : ℕ) :
    LinearMap.det (Algebra.lmul ℝ ℂ (-(FrobeniusSimilitude.frobeniusMultiplier θ m ^ k)))
      = (m : ℝ) ^ k := by
  rw [← Algebra.norm_apply, Algebra.norm_complex_apply, Complex.normSq_neg, map_pow,
    Complex.normSq_eq_norm_sq, FrobeniusSimilitude.norm_frobeniusMultiplier,
    Real.sq_sqrt (Nat.cast_nonneg m)]

end CriticalLinePhasor.LeafwiseConformalPurity

#print axioms CriticalLinePhasor.LeafwiseConformalPurity.purity_of_cup_conformal
#print axioms CriticalLinePhasor.LeafwiseConformalPurity.deninger_conformal_purity
#print axioms CriticalLinePhasor.LeafwiseConformalPurity.frobeniusSimilitude_hermitian
#print axioms CriticalLinePhasor.LeafwiseConformalPurity.frobeniusSimilitude_det
#print axioms CriticalLinePhasor.LeafwiseConformalPurity.conformalFlow_hermitian
#print axioms CriticalLinePhasor.LeafwiseConformalPurity.norm_frobeniusMultiplier_eq_flow
#print axioms CriticalLinePhasor.LeafwiseConformalPurity.lefschetz_sign_pos
#print axioms CriticalLinePhasor.LeafwiseConformalPurity.lefschetz_weight_neg
