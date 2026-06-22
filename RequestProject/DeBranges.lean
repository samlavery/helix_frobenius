import Mathlib

/-!
# de Branges / Hermite–Biehler structure functions

The Hermite–Biehler spectral framework: a structure function `E`, its reflection `E*`, the real
components `A, B`, and the Hermite–Biehler positivity `IsHB`.  The content is that `IsHB E` forces
the zeros of `A` and `B` to be **real** and (for entire `E`) **discrete** — a real, discrete
spectrum from the positivity.  A worked example is the Paley–Wiener function `E(z)=e^{-iz}`, whose
`B`-component is `sin` with spectrum `{kπ}`.

Mathlib-only; self-contained.
-/

open Complex
open scoped ComplexConjugate

namespace CriticalLinePhasor.DeBranges
noncomputable section

/-! ## Gram positivity (the positive-definite reproducing kernel fact) -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The Gram quadratic form `∑ᵢⱼ conj(cᵢ)·cⱼ·⟪vᵢ,vⱼ⟫` equals `⟪∑ cᵢ•vᵢ, ∑ cⱼ•vⱼ⟫` — the algebraic
identity behind positive-definite (reproducing-kernel) de Branges spaces. -/
theorem gram_quadratic_form_eq_inner_self {n : ℕ} (v : Fin n → H) (c : Fin n → ℂ) :
    ∑ i, ∑ j, (starRingEnd ℂ) (c i) * c j * (inner ℂ (v i) (v j)) =
      (inner ℂ (∑ i, c i • v i) (∑ j, c j • v j) : ℂ) := by
  simp +decide only [starRingEnd_apply, inner_sum, sum_inner];
  simp +decide only [mul_assoc, inner_smul_right, inner_smul_left, starRingEnd_apply];
  exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [ ← inner_conj_symm ] ; simp +decide [ mul_assoc, mul_comm ] )

/-- The Gram quadratic form is real and nonnegative (positive semidefiniteness). -/
theorem gram_quadratic_form_nonneg {n : ℕ} (v : Fin n → H) (c : Fin n → ℂ) :
    0 ≤ (∑ i, ∑ j, (starRingEnd ℂ) (c i) * c j * (inner ℂ (v i) (v j))).re := by
  rw [ gram_quadratic_form_eq_inner_self ];
  rw [ inner_self_eq_norm_sq_to_K ] ; norm_num;
  norm_cast ; positivity

/-! ## Hermite–Biehler structure functions and their components -/

/-- The reflected function `E*(z) = conj (E (conj z))`, the second generator of `H(E)`. -/
def Estar (E : ℂ → ℂ) (z : ℂ) : ℂ := (starRingEnd ℂ) (E ((starRingEnd ℂ) z))

/-- `E*` is an involution: `(E*)* = E`. -/
@[simp] theorem Estar_Estar (E : ℂ → ℂ) : Estar (Estar E) = E := by
  exact funext fun x => by simp +decide [ Estar ] ;

/-- `‖E* z‖ = ‖E (conj z)‖`. -/
theorem norm_Estar (E : ℂ → ℂ) (z : ℂ) : ‖Estar E z‖ = ‖E ((starRingEnd ℂ) z)‖ := by
  exact Complex.norm_conj _

/-- The `A`-component `A = (E + E*)/2` (real-entire). -/
def Acomp (E : ℂ → ℂ) (z : ℂ) : ℂ := (E z + Estar E z) / 2

/-- The `B`-component `B = i (E − E*)/2` (real-entire); its zeros are the de Branges spectrum. -/
def Bcomp (E : ℂ → ℂ) (z : ℂ) : ℂ := Complex.I * (E z - Estar E z) / 2

/-- Hermite–Biehler class: `E` dominates its reflection on the open upper half-plane. -/
def IsHB (E : ℂ → ℂ) : Prop := ∀ z : ℂ, 0 < z.im → ‖Estar E z‖ < ‖E z‖

/-! ## The positivity forces reality and discreteness of the spectrum -/

/-- On the lower half-plane the inequality reverses: `‖E z‖ < ‖E* z‖`. -/
theorem hb_lower {E : ℂ → ℂ} (hE : IsHB E) {z : ℂ} (hz : z.im < 0) :
    ‖E z‖ < ‖Estar E z‖ := by
  have := hE ( starRingEnd ℂ z ) ?_ <;> simp_all +decide;
  unfold Estar at * ; aesop

/-- A Hermite–Biehler function has no zeros in the open upper half-plane. -/
theorem hb_no_zero_upper {E : ℂ → ℂ} (hE : IsHB E) {z : ℂ} (hz : 0 < z.im) : E z ≠ 0 := by
  exact fun h => absurd ( hE z hz ) ( by norm_num [ h ] )

/-- For Hermite–Biehler `E`, `‖E z‖ = ‖E* z‖` forces `z` onto the real axis. -/
theorem norm_eq_imp_im_zero {E : ℂ → ℂ} (hE : IsHB E) {z : ℂ}
    (h : ‖E z‖ = ‖Estar E z‖) : z.im = 0 := by
  contrapose! h;
  cases lt_or_gt_of_ne h <;> [ exact ne_of_lt ( hb_lower hE ‹_› ) ; exact ne_of_gt ( hE z ‹_› ) ]

/-- Every zero of `A` is real. -/
theorem Acomp_zero_im_eq_zero {E : ℂ → ℂ} (hE : IsHB E) {z : ℂ} (hz : Acomp E z = 0) :
    z.im = 0 := by
  unfold Acomp at hz; simp_all +decide [ div_eq_iff ] ;
  exact norm_eq_imp_im_zero hE ( by rw [ eq_neg_of_add_eq_zero_left hz ] ; norm_num )

/-- Every zero of `B` is real: the spectrum is real, from the positivity. -/
theorem Bcomp_zero_im_eq_zero {E : ℂ → ℂ} (hE : IsHB E) {z : ℂ} (hz : Bcomp E z = 0) :
    z.im = 0 := by
  convert CriticalLinePhasor.DeBranges.norm_eq_imp_im_zero hE _;
  unfold Bcomp at hz; simp_all +decide ;
  simp_all +decide [ Complex.normSq, Complex.norm_def, sub_eq_zero ]

/-- `B` is not identically zero for Hermite–Biehler `E`. -/
theorem Bcomp_not_eventually_zero {E : ℂ → ℂ} (hE : IsHB E) :
    ∃ z : ℂ, Bcomp E z ≠ 0 := by
  by_contra! h;
  have := Bcomp_zero_im_eq_zero hE ( h Complex.I ) ; norm_num at this;

/-- If `E` is entire so is its reflection `E*` (Schwarz reflection). -/
theorem Estar_analyticOnNhd {E : ℂ → ℂ} (hEnt : AnalyticOnNhd ℂ E Set.univ) :
    AnalyticOnNhd ℂ (Estar E) Set.univ := by
  apply DifferentiableOn.analyticOnNhd _ isOpen_univ
  intro z _
  have hd := (hEnt ((starRingEnd ℂ) z) (Set.mem_univ _)).differentiableAt
  have hdd := hd.hasDerivAt.conj_conj
  rw [Complex.conj_conj] at hdd
  exact hdd.differentiableAt.differentiableWithinAt

/-- The `B`-component of an entire function is entire. -/
theorem Bcomp_analyticOnNhd {E : ℂ → ℂ} (hEnt : AnalyticOnNhd ℂ E Set.univ) :
    AnalyticOnNhd ℂ (Bcomp E) Set.univ := by
  apply_rules [ AnalyticOnNhd.div, AnalyticOnNhd.mul, analyticOnNhd_const ];
  · apply_rules [ AnalyticOnNhd.sub, hEnt, Estar_analyticOnNhd ];
  · norm_num

/-- For entire Hermite–Biehler `E`, the zeros of `B` are isolated: a discrete spectrum. -/
theorem Bcomp_zeros_discrete {E : ℂ → ℂ} (hEnt : AnalyticOnNhd ℂ E Set.univ)
    (hE : IsHB E) (z₀ : ℂ) :
    ∀ᶠ z in nhdsWithin z₀ {z₀}ᶜ, Bcomp E z ≠ 0 := by
  by_contra h;
  have h_id : AnalyticOnNhd ℂ (Bcomp E) Set.univ → (∃ᶠ z in nhdsWithin z₀ {z₀}ᶜ, Bcomp E z = 0) → ∀ z, Bcomp E z = 0 := by
    intros h_analytic h_frequently_zero z
    apply AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero h_analytic (isPreconnected_univ) (Set.mem_univ z₀) h_frequently_zero;
    trivial;
  exact absurd ( h_id ( CriticalLinePhasor.DeBranges.Bcomp_analyticOnNhd hEnt ) ( by simpa using h ) ) ( by simpa using CriticalLinePhasor.DeBranges.Bcomp_not_eventually_zero hE )

/-! ## Helix / anti-helix domination

`E` and its reflection `E*` are the *helix* and the *anti-helix*.  On the real axis they are
balanced, `‖E z‖ = ‖E* z‖` (no domination).  Off the real axis the positivity `IsHB E` forces a
strict **domination**: in the open upper half-plane the helix dominates (`‖E* z‖ < ‖E z‖`), in the
open lower half-plane the anti-helix dominates (`‖E z‖ < ‖E* z‖`).  Consequently an off-axis point
can never be balanced, so an off-line/off-axis spectral zero — which is exactly a balance point of
the helix and anti-helix — cannot exist: the two helices cannot conspire to both meet (a zero) and
retain no domination away from the real axis. -/

/-- A spectral zero is exactly a balance point of the helix and anti-helix: `B z = 0 ↔ E z = E* z`. -/
theorem Bcomp_eq_zero_iff (E : ℂ → ℂ) (z : ℂ) : Bcomp E z = 0 ↔ E z = Estar E z := by
  unfold Bcomp
  rw [div_eq_zero_iff]
  simp [Complex.I_ne_zero, sub_eq_zero]

/-- **Domination dichotomy.**  Off the real axis exactly one helix strictly dominates the other:
in the upper half-plane the helix dominates, in the lower half-plane the anti-helix dominates. -/
theorem hb_domination_dichotomy {E : ℂ → ℂ} (hE : IsHB E) {z : ℂ} (hz : z.im ≠ 0) :
    ‖Estar E z‖ < ‖E z‖ ∨ ‖E z‖ < ‖Estar E z‖ := by
  rcases lt_or_gt_of_ne hz with h | h
  · exact Or.inr (hb_lower hE h)
  · exact Or.inl (hE z h)

/-- **No off-axis balance.**  Away from the real axis the helix and anti-helix can never be
balanced; one is forced to dominate. -/
theorem hb_no_offaxis_balance {E : ℂ → ℂ} (hE : IsHB E) {z : ℂ} (hz : z.im ≠ 0) :
    ‖E z‖ ≠ ‖Estar E z‖ := fun h => hz (norm_eq_imp_im_zero hE h)

/-- **No off-line spectral zero.**  A spectral zero (a balance point of helix and anti-helix)
cannot lie off the real axis: the two helices cannot conspire to both vanish-balance and retain no
domination. -/
theorem hb_no_offaxis_spectral_zero {E : ℂ → ℂ} (hE : IsHB E) {z : ℂ} (hz : z.im ≠ 0) :
    Bcomp E z ≠ 0 := fun h => hz (Bcomp_zero_im_eq_zero hE h)

/-! ## A concrete Hermite–Biehler structure function: Paley–Wiener -/

/-- The Paley–Wiener structure function `E(z) = e^{−i z}`. -/
def paleyWiener (z : ℂ) : ℂ := Complex.exp (-(Complex.I * z))

/-- Its reflection is `E*(z) = e^{i z}`. -/
theorem paleyWiener_Estar : Estar paleyWiener = fun z => Complex.exp (Complex.I * z) := by
  funext z; simp [Estar, paleyWiener];
  simp +decide [ Complex.ext_iff, Complex.exp_re, Complex.exp_im ]

/-- `e^{−i z}` is a Hermite–Biehler function. -/
theorem paleyWiener_isHB : IsHB paleyWiener := by
  intro z hz;
  norm_num [ paleyWiener_Estar, paleyWiener ];
  norm_num [ Complex.norm_exp, hz ]

/-- The `B`-component of the Paley–Wiener function is `sin`; its zeros `{kπ}` are the spectrum. -/
theorem paleyWiener_Bcomp : Bcomp paleyWiener = Complex.sin := by
  ext1 z
  rw [Bcomp, paleyWiener_Estar]
  simp only [paleyWiener, Complex.sin]
  ring_nf

/-! ## The critical-line change of variables -/

/-- The change of variables `z = −i(ρ − ½)` has `im z = ½ − Re ρ`, so `z` is real iff `ρ` lies on
the critical line `Re ρ = ½`. -/
theorem deBranges_var_im (ρ : ℂ) : (-(Complex.I * (ρ - 1 / 2))).im = 1 / 2 - ρ.re := by
  norm_num [ Complex.ext_iff ]

end
end CriticalLinePhasor.DeBranges
