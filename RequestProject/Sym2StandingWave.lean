import RequestProject.Sym2RegistrationLanding
import RequestProject.SchwarzAxisReality

/-!
# The r = 2 standing wave at the pair level: axis reality of the peeled Sym² readout

Composition layer on top of `Sym2RegistrationLanding.lean` (the compiled peeled FE and
Γ-chart readout).  Everything proven here is unconditional.  The chain:

* `peeledFE_quotient` — the peeled functional equation in quotient form, global:
  `Λ̄(1−s)/Λζ(1−s) = Λ̄(s)/Λζ(s)` for every `s ∈ ℂ` (at zeros of `Λζ` both sides carry
  the same value by the division convention, so no side condition is needed).
* `sym2Display` / `peeled_readout_eq_display` — the peeled object in its own degree-3
  chart with the `Λζ`-factor `Γℝ(s)` split off:
  `mellin (peeledProfile k f) s = Γℝ(s) · sym2Display k f s` on `2 < Re s`.
* `peeled_edge_regularity` — the edge value: `ζ(s)⁻¹·Λ̄(s) → ‖f‖²` as `s → 1`; the pole
  of `Λ̄` at the edge is exactly cancelled by the peeled ζ (Rankin's theorem shape: the
  peeled Sym² readout is regular at `s = 1` with value the Petersson mass).
* `mellin_conj_of_conjFixed` / `rsAveraged_lambda_conj_halfplane` — Schwarz symmetry of
  the Mellin readout of the real-valued averaged tail on `1 < Re s`.
* `entire_conj_reflection` — the identity-theorem transporter: an entire function
  Schwarz-symmetric on the half-plane `1 < Re s` is Schwarz-symmetric everywhere.
* `rsAveraged_lambda_conj` — **global Schwarz symmetry of the completed averaged
  transform**: `Λ̄(s̄) = conj (Λ̄ s)` for every `s ∈ ℂ`, through the entire part `Λ₀`
  and back down to `Λ̄` (the pole corrections conjugate term-by-term).
* `rsAveraged_standingWave` / `rsAveraged_axis_im_zero` — **the r = 2 standing wave at
  the pair level**: on the weld axis `Re s = 1/2` the completed averaged transform is
  real — Schwarz symmetry welded to the compiled self-dual reflection `Λ̄(1−s) = Λ̄(s)`.
* `Gammaℝ_conj` / `completedRiemannZeta_conj` — Schwarz symmetry of the deligne factor
  and of `Λζ` (via the same identity-theorem transporter on `Λζ₀`).
* `peeledQuotient_standingWave` / `peeledQuotient_axis_im_zero` — **the peeled standing
  wave**: on `Re s = 1/2` the peeled quotient `Λ̄(s)/Λζ(s)` is real — the axis reality
  of the ζ-peeled Sym²-bank readout, in the `AxisReality.fe_of_axisReality` input shape
  with `ε = 1`.
-/

open MeasureTheory Complex UpperHalfPlane ModularGroup Set Filter ArithmeticFunction
open scoped Real MatrixGroups Topology LSeries.notation ArithmeticFunction.Moebius
  ComplexConjugate

namespace CriticalLinePhasor.Sym2Registration

open CriticalLinePhasor.Unfolding CriticalLinePhasor.HeckeSupBound
  CriticalLinePhasor.EpsteinTheta CriticalLinePhasor.CarrierTheta CriticalLinePhasor.ZetaPeel

variable {k : ℤ}

/-! ## The peeled functional equation in quotient form -/

/-- **The peeled functional equation in quotient form**, global: for every `s ∈ ℂ`,

  `Λ̄(1−s)/Λζ(1−s) = Λ̄(s)/Λζ(s)`

— the reflection identity of the peeled quotient `Λ̄/Λζ`, from the compiled self-dual
reflection of the averaged pair and the reflection of the completed ζ.  At zeros of `Λζ`
both sides carry the same value by the division convention, so no side condition is
needed. -/
theorem peeledFE_quotient (f : CuspForm 𝒮ℒ k) (hk : 0 ≤ k) (s : ℂ) :
    (rsAveragedWeakFEPair f hk).Λ (1 - s) / completedRiemannZeta (1 - s) =
      (rsAveragedWeakFEPair f hk).Λ s / completedRiemannZeta s := by
  rw [rsAveraged_selfdual_FE f hk s, completedRiemannZeta_one_sub]

/-! ## The display chart -/

/-- **The Sym² display**: the peeled readout in its own degree-3 `Γℝ`-chart, the `Λζ`
chart factor `Γℝ(s)` split off — `2^{−k}·ζ(2s)·Γℝ(s+1)·Γℝ(s+k−1)·Γℝ(s+k)·L(μ ⋆ b, s)`
with `b_n = ‖a_n‖²/n^{k−1}` the Deligne-normalized Rankin square.  Identifying
`ζ(2s)·L(μ ⋆ b, s)` with the Sym²-Satake Euler product is Hecke multiplicativity — not
proven in this file. -/
noncomputable def sym2Display (k : ℤ) (f : CuspForm 𝒮ℒ k) (s : ℂ) : ℂ :=
  (2 : ℂ) ^ (-(k : ℂ)) * riemannZeta (2 * s) *
    (Gammaℝ (s + 1) * Gammaℝ (s + (k : ℂ) - 1) * Gammaℝ (s + (k : ℂ))) *
    LSeries (⇑((μ : ArithmeticFunction ℂ) * rankinSquareNorm f)) s

/-- **The peeled readout is the display in the `Γℝ(s)`-chart** on `2 < Re s`:
`mellin (θ_μ(θ̄_f − ‖f‖²)) s = Γℝ(s) · sym2Display k f s` — a regrouping of the compiled
degree-4 landing isolating the peeled ζ's own chart factor. -/
theorem peeled_readout_eq_display (f : CuspForm 𝒮ℒ k) (hk : 0 ≤ k) {s : ℂ}
    (hs : 2 < s.re) :
    mellin (peeledProfile k f) s = Gammaℝ s * sym2Display k f s := by
  rw [peeled_readout_gammaChart f hk hs, sym2Display]
  ring

/-! ## Edge regularity: the peeled readout at `s = 1` -/

/-- **Edge regularity of the peeled readout** (Rankin's theorem shape): as `s → 1`,

  `ζ(s)⁻¹ · Λ̄(s) → ‖f‖²`

— the simple pole of the completed averaged transform at the edge is exactly cancelled
by the peeled ζ-factor, and the regularized edge value is the Petersson mass. -/
theorem peeled_edge_regularity (f : CuspForm 𝒮ℒ k) (hk : 0 ≤ k) :
    Tendsto (fun s : ℂ => (riemannZeta s)⁻¹ * (rsAveragedWeakFEPair f hk).Λ s)
      (𝓝[≠] 1) (𝓝 ((peterssonMass k f : ℝ) : ℂ)) := by
  have h1 : Tendsto (fun s : ℂ => ((s - 1) * riemannZeta s)⁻¹) (𝓝[≠] 1)
      (𝓝 (1 : ℂ)) := by
    have h := (riemannZeta_residue_one.inv₀ one_ne_zero)
    simpa using h
  have h3 := h1.mul (rsAveraged_residue_one f hk)
  rw [one_mul] at h3
  refine h3.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  calc ((s - 1) * riemannZeta s)⁻¹ * ((s - 1) * (rsAveragedWeakFEPair f hk).Λ s)
      = ((s - 1)⁻¹ * (s - 1)) * ((riemannZeta s)⁻¹ * (rsAveragedWeakFEPair f hk).Λ s) := by
        rw [mul_inv]; ring
    _ = (riemannZeta s)⁻¹ * (rsAveragedWeakFEPair f hk).Λ s := by
        rw [inv_mul_cancel₀ hs1, one_mul]

/-! ## Schwarz symmetry of the Mellin readout -/

/-- The Mellin transform of a conjugation-fixed (real-valued) profile is
Schwarz-symmetric: `mellin g (s̄) = conj (mellin g s)`. -/
lemma mellin_conj_of_conjFixed {g : ℝ → ℂ} (hg : ∀ t : ℝ, 0 < t → conj (g t) = g t)
    (s : ℂ) : mellin g (conj s) = conj (mellin g s) := by
  rw [show mellin g (conj s) = ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (conj s - 1) • g t from rfl,
    show mellin g s = ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) • g t from rfl,
    ← integral_conj]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have harg : ((t : ℂ)).arg ≠ π := by
    rw [Complex.arg_ofReal_of_nonneg (le_of_lt ht)]
    exact Ne.symm Real.pi_ne_zero
  have hcpow : ((t : ℂ)) ^ (conj (s - 1)) = conj ((t : ℂ) ^ (s - 1)) := by
    have h := Complex.cpow_conj ((t : ℂ)) (s - 1) harg
    rwa [Complex.conj_ofReal] at h
  rw [show conj s - 1 = conj (s - 1) from by rw [map_sub, map_one]]
  rw [smul_eq_mul, smul_eq_mul, map_mul, hcpow, hg t ht]

/-- **Schwarz symmetry of the completed averaged transform on the readout half-plane**:
for `1 < Re s`, `Λ̄(s̄) = conj (Λ̄ s)` — the averaged tail is real-valued, so its Mellin
readout conjugates through the integral. -/
lemma rsAveraged_lambda_conj_halfplane (f : CuspForm 𝒮ℒ k) (hk : 0 ≤ k) {s : ℂ}
    (hs : 1 < s.re) :
    (rsAveragedWeakFEPair f hk).Λ (conj s) = conj ((rsAveragedWeakFEPair f hk).Λ s) := by
  have hs' : 1 < (conj s).re := by rwa [Complex.conj_re]
  rw [← rsAveraged_mellin_eq f hk hs', ← rsAveraged_mellin_eq f hk hs]
  refine mellin_conj_of_conjFixed (fun t ht => ?_) s
  simp only [averagedThetaC, map_sub, Complex.conj_ofReal]

/-! ## The identity-theorem transporter -/

/-- **Entire Schwarz symmetry from half-plane Schwarz symmetry**: an entire function
that is Schwarz-symmetric on `1 < Re s` is Schwarz-symmetric on the whole plane, by the
identity theorem on the connected plane applied to `F` and `s ↦ conj (F s̄)`. -/
theorem entire_conj_reflection {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (hhalf : ∀ s : ℂ, 1 < s.re → F (conj s) = conj (F s)) (s : ℂ) :
    F (conj s) = conj (F s) := by
  have hH : Differentiable ℂ fun z : ℂ => conj (F (conj z)) :=
    CriticalLinePhasor.AxisReality.differentiable_conj_conj hF
  have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have h2 : (2 : ℂ) ∈ {z : ℂ | 1 < z.re} := by
    simp only [Set.mem_setOf_eq]
    norm_num
  have hagree : ∀ z ∈ {z : ℂ | 1 < z.re}, F z = conj (F (conj z)) := fun z hz => by
    rw [hhalf z hz, Complex.conj_conj]
  have hev : ∀ᶠ z in 𝓝 (2 : ℂ), F z = conj (F (conj z)) :=
    eventually_of_mem (hopen.mem_nhds h2) hagree
  have hfreq : ∃ᶠ z in 𝓝[≠] (2 : ℂ), F z = conj (F (conj z)) :=
    (hev.filter_mono nhdsWithin_le_nhds).frequently
  have hEq := AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq
    (hF.differentiableOn.analyticOnNhd isOpen_univ)
    (hH.differentiableOn.analyticOnNhd isOpen_univ)
    isPreconnected_univ (Set.mem_univ (2 : ℂ)) hfreq
  have h := hEq (Set.mem_univ (conj s))
  simp only [Complex.conj_conj] at h
  exact h

/-! ## Global Schwarz symmetry of the completed averaged transform -/

/-- The entire part of the averaged pair in explicit pole-corrected form:
`Λ₀(z) = Λ̄(z) + (1/z)·‖f‖² + (1/(1−z))·‖f‖²`. -/
lemma rsAveraged_lambda₀_formula (f : CuspForm 𝒮ℒ k) (hk : 0 ≤ k) (z : ℂ) :
    (rsAveragedWeakFEPair f hk).Λ₀ z =
      (rsAveragedWeakFEPair f hk).Λ z + (1 / z) * ((peterssonMass k f : ℝ) : ℂ) +
        (1 / (1 - z)) * ((peterssonMass k f : ℝ) : ℂ) := by
  have h := (rsAveragedWeakFEPair f hk).Λ₀_eq z
  have hf₀ : (rsAveragedWeakFEPair f hk).f₀ = ((peterssonMass k f : ℝ) : ℂ) := rfl
  rw [hf₀, rsAveragedWeakFEPair_g₀, rsAveragedWeakFEPair_ε, rsAveragedWeakFEPair_k] at h
  simpa [smul_eq_mul] using h

/-- Global Schwarz symmetry of the entire part: `Λ₀(s̄) = conj (Λ₀ s)` for every `s`,
by the identity-theorem transporter from the half-plane symmetry. -/
lemma rsAveraged_lambda₀_conj (f : CuspForm 𝒮ℒ k) (hk : 0 ≤ k) (s : ℂ) :
    (rsAveragedWeakFEPair f hk).Λ₀ (conj s) = conj ((rsAveragedWeakFEPair f hk).Λ₀ s) := by
  refine entire_conj_reflection (rsAveraged_entirePart_differentiable f hk)
    (fun z hz => ?_) s
  rw [rsAveraged_lambda₀_formula f hk (conj z), rsAveraged_lambda₀_formula f hk z,
    rsAveraged_lambda_conj_halfplane f hk hz]
  simp only [map_add, map_mul, map_div₀, map_one, map_sub, Complex.conj_ofReal]

/-- **Global Schwarz symmetry of the completed averaged transform**: for every `s ∈ ℂ`,

  `Λ̄(s̄) = conj (Λ̄ s)`

— through the entire part and back down, the pole corrections conjugating
term-by-term. -/
theorem rsAveraged_lambda_conj (f : CuspForm 𝒮ℒ k) (hk : 0 ≤ k) (s : ℂ) :
    (rsAveragedWeakFEPair f hk).Λ (conj s) = conj ((rsAveragedWeakFEPair f hk).Λ s) := by
  have h1 := rsAveraged_lambda₀_formula f hk (conj s)
  have h2c := congrArg conj (rsAveraged_lambda₀_formula f hk s)
  simp only [map_add, map_mul, map_div₀, map_one, map_sub, Complex.conj_ofReal] at h2c
  rw [rsAveraged_lambda₀_conj f hk s] at h1
  linear_combination h2c - h1

/-! ## The standing wave at the pair level -/

/-- On the weld axis `Re s = 1/2` the Schwarz reflection is the functional-equation
reflection: `s̄ = 1 − s`. -/
lemma conj_eq_one_sub_of_axis {s : ℂ} (hs : s.re = 1 / 2) : conj s = 1 - s := by
  apply Complex.ext
  · rw [Complex.conj_re, Complex.sub_re, Complex.one_re, hs]
    norm_num
  · rw [Complex.conj_im, Complex.sub_im, Complex.one_im]
    ring

/-- **The r = 2 standing wave at the pair level**: on the weld axis `Re s = 1/2` the
completed averaged transform is fixed by conjugation,

  `conj (Λ̄ s) = Λ̄ s`

— global Schwarz symmetry welded to the compiled self-dual reflection
`Λ̄(1−s) = Λ̄(s)`. -/
theorem rsAveraged_standingWave (f : CuspForm 𝒮ℒ k) (hk : 0 ≤ k) {s : ℂ}
    (hs : s.re = 1 / 2) :
    conj ((rsAveragedWeakFEPair f hk).Λ s) = (rsAveragedWeakFEPair f hk).Λ s := by
  rw [← rsAveraged_lambda_conj f hk s, conj_eq_one_sub_of_axis hs,
    rsAveraged_selfdual_FE f hk s]

/-- The standing wave in real form: `Λ̄` is real on the weld axis. -/
theorem rsAveraged_axis_im_zero (f : CuspForm 𝒮ℒ k) (hk : 0 ≤ k) {s : ℂ}
    (hs : s.re = 1 / 2) : ((rsAveragedWeakFEPair f hk).Λ s).im = 0 :=
  Complex.conj_eq_iff_im.mp (rsAveraged_standingWave f hk hs)

/-! ## Schwarz symmetry of the completed ζ and the peeled standing wave -/

/-- Schwarz symmetry of the Deligne chart factor: `Γℝ(s̄) = conj (Γℝ s)`. -/
lemma Gammaℝ_conj (s : ℂ) : Gammaℝ (conj s) = conj (Gammaℝ s) := by
  rw [Gammaℝ_def, Gammaℝ_def]
  have harg : ((π : ℝ) : ℂ).arg ≠ π := by
    rw [Complex.arg_ofReal_of_nonneg Real.pi_pos.le]
    exact Ne.symm Real.pi_ne_zero
  have hdiv : -conj s / 2 = conj (-s / 2) := by
    rw [map_div₀, map_neg, map_ofNat]
  have hdiv2 : conj s / 2 = conj (s / 2) := by
    rw [map_div₀, map_ofNat]
  rw [hdiv, hdiv2, Complex.Gamma_conj, map_mul]
  congr 1
  have h := Complex.cpow_conj (((π : ℝ) : ℂ)) (-s / 2) harg
  rwa [Complex.conj_ofReal] at h

/-- Schwarz symmetry of the completed ζ on `1 < Re s`, where `Λζ = ζ·Γℝ` and both
factors conjugate. -/
lemma completedRiemannZeta_conj_halfplane {s : ℂ} (hs : 1 < s.re) :
    completedRiemannZeta (conj s) = conj (completedRiemannZeta s) := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    norm_num [Complex.zero_re] at hs
  have hcs0 : conj s ≠ 0 := by
    intro h
    apply hs0
    simpa using congrArg conj h
  have hΓ : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by linarith)
  have hΓ' : Gammaℝ (conj s) ≠ 0 :=
    Gammaℝ_ne_zero_of_re_pos (by rw [Complex.conj_re]; linarith)
  have h1 : completedRiemannZeta s = riemannZeta s * Gammaℝ s := by
    rw [riemannZeta_def_of_ne_zero hs0]
    field_simp
  have h2 : completedRiemannZeta (conj s) = riemannZeta (conj s) * Gammaℝ (conj s) := by
    rw [riemannZeta_def_of_ne_zero hcs0]
    field_simp
  rw [h1, h2, riemannZeta_conj, Gammaℝ_conj, map_mul]

/-- Global Schwarz symmetry of the entire completed ζ: `Λζ₀(s̄) = conj (Λζ₀ s)`. -/
lemma completedRiemannZeta₀_conj (s : ℂ) :
    completedRiemannZeta₀ (conj s) = conj (completedRiemannZeta₀ s) := by
  refine entire_conj_reflection differentiable_completedZeta₀ (fun z hz => ?_) s
  have h1' : completedRiemannZeta₀ z = completedRiemannZeta z + 1 / z + 1 / (1 - z) := by
    linear_combination (-1 : ℂ) * completedRiemannZeta_eq z
  have h2' : completedRiemannZeta₀ (conj z) =
      completedRiemannZeta (conj z) + 1 / conj z + 1 / (1 - conj z) := by
    linear_combination (-1 : ℂ) * completedRiemannZeta_eq (conj z)
  rw [h2', completedRiemannZeta_conj_halfplane hz, h1']
  simp only [map_add, map_div₀, map_one, map_sub]

/-- **Global Schwarz symmetry of the completed ζ**: `Λζ(s̄) = conj (Λζ s)` for every
`s ∈ ℂ`. -/
theorem completedRiemannZeta_conj (s : ℂ) :
    completedRiemannZeta (conj s) = conj (completedRiemannZeta s) := by
  rw [completedRiemannZeta_eq (conj s), completedRiemannZeta_eq s,
    completedRiemannZeta₀_conj s]
  simp only [map_sub, map_div₀, map_one]

/-- **The peeled standing wave**: on the weld axis `Re s = 1/2` the peeled quotient is
fixed by conjugation,

  `conj (Λ̄(s)/Λζ(s)) = Λ̄(s)/Λζ(s)`

— the axis reality of the ζ-peeled Sym²-bank readout, the `r = 2` standing-wave content
at the pair level in the `fe_of_axisReality` input shape with `ε = 1`.  At zeros of `Λζ`
on the axis both sides carry the same value by the division convention. -/
theorem peeledQuotient_standingWave (f : CuspForm 𝒮ℒ k) (hk : 0 ≤ k) {s : ℂ}
    (hs : s.re = 1 / 2) :
    conj ((rsAveragedWeakFEPair f hk).Λ s / completedRiemannZeta s) =
      (rsAveragedWeakFEPair f hk).Λ s / completedRiemannZeta s := by
  rw [map_div₀, rsAveraged_standingWave f hk hs, ← completedRiemannZeta_conj,
    conj_eq_one_sub_of_axis hs, completedRiemannZeta_one_sub]

/-- The peeled standing wave in real form: `Λ̄/Λζ` is real on the weld axis. -/
theorem peeledQuotient_axis_im_zero (f : CuspForm 𝒮ℒ k) (hk : 0 ≤ k) {s : ℂ}
    (hs : s.re = 1 / 2) :
    ((rsAveragedWeakFEPair f hk).Λ s / completedRiemannZeta s).im = 0 :=
  Complex.conj_eq_iff_im.mp (peeledQuotient_standingWave f hk hs)

end CriticalLinePhasor.Sym2Registration

#print axioms CriticalLinePhasor.Sym2Registration.peeledFE_quotient
#print axioms CriticalLinePhasor.Sym2Registration.sym2Display
#print axioms CriticalLinePhasor.Sym2Registration.peeled_readout_eq_display
#print axioms CriticalLinePhasor.Sym2Registration.peeled_edge_regularity
#print axioms CriticalLinePhasor.Sym2Registration.mellin_conj_of_conjFixed
#print axioms CriticalLinePhasor.Sym2Registration.rsAveraged_lambda_conj_halfplane
#print axioms CriticalLinePhasor.Sym2Registration.entire_conj_reflection
#print axioms CriticalLinePhasor.Sym2Registration.rsAveraged_lambda₀_formula
#print axioms CriticalLinePhasor.Sym2Registration.rsAveraged_lambda₀_conj
#print axioms CriticalLinePhasor.Sym2Registration.rsAveraged_lambda_conj
#print axioms CriticalLinePhasor.Sym2Registration.conj_eq_one_sub_of_axis
#print axioms CriticalLinePhasor.Sym2Registration.rsAveraged_standingWave
#print axioms CriticalLinePhasor.Sym2Registration.rsAveraged_axis_im_zero
#print axioms CriticalLinePhasor.Sym2Registration.Gammaℝ_conj
#print axioms CriticalLinePhasor.Sym2Registration.completedRiemannZeta_conj_halfplane
#print axioms CriticalLinePhasor.Sym2Registration.completedRiemannZeta₀_conj
#print axioms CriticalLinePhasor.Sym2Registration.completedRiemannZeta_conj
#print axioms CriticalLinePhasor.Sym2Registration.peeledQuotient_standingWave
#print axioms CriticalLinePhasor.Sym2Registration.peeledQuotient_axis_im_zero
