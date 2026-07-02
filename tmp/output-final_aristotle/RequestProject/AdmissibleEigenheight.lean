import Mathlib
import RequestProject.GeometricPhasorClosure

/-!
# Admissible source-height eigenheights and Rouché focal-zero stability

This file records two requested "next theorems", both **pure analysis** (no RH/GRH input):

## 1. The admissibility theorem (real positive source-height ⇒ critical line)

The source-height dictionary attaches to a positive geometric height `Z` the spectral readout
`s = criticalReadout Z = 1/2 + i·log Z`.  For *real* `Z` the readout always has real part `1/2`,
so a zero `ρ` that is *represented by an admissible real height* must lie on the critical line.

* `admissible_re_half` — if `ρ = criticalReadout Z` for a real `Z`, then `Re ρ = 1/2`.
* `admissible_iff_re_half` — a complex number is an admissible real-height readout **iff** it lies
  on the critical line `Re ρ = 1/2`.  (Backward direction: take `Z = exp (Im ρ)`.)
* `offline_not_admissible` — an off-line `ρ` (`Re ρ ≠ 1/2`) admits **no** real source-height.
* `height_solving_readout`, `height_im` — the (in general complex) height solving
  `1/2 + w·i = ρ` is `w = ρ.im - (ρ.re - 1/2)·i`; its imaginary part is `-(Re ρ - 1/2)`, so the
  height is real exactly when `Re ρ = 1/2`.  This is the precise sense in which an off-line zero
  "forces a complex source-height".

The remaining bridge to RH/GRH is **not** self-adjointness; it is the (unproved) representability
statement *every nontrivial zero is an admissible source-height eigenheight*, packaged as
`EveryZeroAdmissible`.  The conditional implication is proved:

* `RH_of_everyZeroAdmissible` — if every nontrivial zero is admissible, then every nontrivial
  zero lies on `Re ρ = 1/2`.

## 2. Rouché / perturbation stability of focal zeros

With the bridge estimate `d = -F + E` and `|E| < |F|` on the boundary, focal zeros track L-zeros.
Mathlib has no packaged Rouché zero-count, so we record the two operative, fully provable halves:

* `focal_no_zero_of_dominant` — **reverse direction** (no L-zero ⇒ no focal zero): wherever the
  L-channel dominates the error (`‖E z‖ < ‖F z‖`), the bridge `d = -F + E` cannot vanish.
* `real_simple_zero_location` — **explicit numerical location bound**: at a simple critical-line
  zero `γ` with `a/2 ≤ F'` and `|E| ≤ ε`, every focal zero `Td` in the window satisfies
  `|Td - γ| ≤ 2ε/a`.
* `real_simple_zero_exists` — **existence**: under `ε < a r / 4` the perturbed pencil `-F + E` has
  a focal zero in `(γ - r, γ + r)` (intermediate value theorem on a sign change), with the same
  `2ε/a` location bound.
* `real_simple_zero_unique` — **existence & uniqueness**: adding the regularity `|E'| < a/2`
  (the real-line analogue of analyticity that makes the perturbed pencil strictly monotone) the
  focal zero in the window is unique.
-/

namespace CriticalLinePhasor.Admissible

open Complex Metric Set Filter Topology
open CriticalLinePhasor CriticalLinePhasor.Geometric

/-! ## 1. The admissibility theorem -/

/-- **Admissibility theorem.**  A zero `ρ` represented by an admissible real positive
source-height eigenheight `Z` (i.e. `ρ = criticalReadout Z`) has real part `1/2`.

(The positivity `0 < Z` is the admissibility domain; the real-part conclusion only uses that `Z`
is real, since then `log Z` is real and contributes only to the imaginary part.) -/
theorem admissible_re_half (ρ : ℂ) (Z : ℝ) (h : ρ = criticalReadout Z) : ρ.re = 1 / 2 := by
  rw [h]; exact criticalReadout_re Z

/-- An off-line `ρ` admits **no** real source-height: there is no real `Z` with
`criticalReadout Z = ρ`. -/
theorem offline_not_admissible (ρ : ℂ) (hρ : ρ.re ≠ 1 / 2) :
    ¬ ∃ Z : ℝ, criticalReadout Z = ρ := by
  rintro ⟨Z, rfl⟩
  exact hρ (criticalReadout_re Z)

/-
**Admissibility characterisation.**  A complex number is an admissible real-height readout
**iff** it lies on the critical line `Re ρ = 1/2`.  The backward direction realises it at the
positive height `Z = exp (Im ρ)`.
-/
theorem admissible_iff_re_half (ρ : ℂ) :
    (∃ Z : ℝ, criticalReadout Z = ρ) ↔ ρ.re = 1 / 2 := by
  constructor;
  · rintro ⟨ Z, rfl ⟩ ; exact criticalReadout_re Z;
  · intro h
    use Real.exp ρ.im;
    unfold criticalReadout; norm_num [ Complex.ext_iff, h ] ;

/-- The (in general complex) analytic height solving the readout equation `1/2 + w·i = ρ`. -/
noncomputable def heightSolvingReadout (ρ : ℂ) : ℂ := ρ.im - (ρ.re - 1 / 2) * I

/-
The height solving the readout equation does solve it: `1/2 + (heightSolvingReadout ρ)·i = ρ`.
-/
theorem height_solving_readout (ρ : ℂ) :
    (1 / 2 : ℂ) + heightSolvingReadout ρ * I = ρ := by
  apply Complex.ext <;>
    simp [heightSolvingReadout, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.sub_re, Complex.sub_im]

/-
**Off-line zeros force a complex source-height.**  The imaginary part of the analytic height
solving the readout equation is `-(Re ρ - 1/2)`; hence the height is real (`Im = 0`) exactly when
`Re ρ = 1/2`.
-/
theorem height_im (ρ : ℂ) : (heightSolvingReadout ρ).im = -(ρ.re - 1 / 2) := by
  unfold heightSolvingReadout; norm_num;

/-! ## 1b. The conditional bridge to RH/GRH -/

/-- A nontrivial zero of the Dirichlet `L`-function (inside the critical strip). -/
def IsNontrivialZero {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (ρ : ℂ) : Prop :=
  DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1

/-- **The representability bridge** (the genuine remaining content of RH/GRH, *not* asserted):
every nontrivial zero is represented by an admissible real positive source-height eigenheight. -/
def EveryZeroAdmissible {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : Prop :=
  ∀ ρ : ℂ, IsNontrivialZero χ ρ → ∃ Z : ℝ, criticalReadout Z = ρ

/-- **Conditional RH/GRH.**  *If* every nontrivial zero is an admissible source-height
eigenheight, then every nontrivial zero lies on the critical line `Re ρ = 1/2`.  The hypothesis is
exactly the unproved representability bridge. -/
theorem RH_of_everyZeroAdmissible {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (h : EveryZeroAdmissible χ) :
    ∀ ρ : ℂ, IsNontrivialZero χ ρ → ρ.re = 1 / 2 := by
  intro ρ hρ
  obtain ⟨Z, hZ⟩ := h ρ hρ
  exact admissible_re_half ρ Z hZ.symm

/-! ## 2. Rouché / perturbation stability of focal zeros -/

/-
**Reverse direction (no L-zero ⇒ no focal zero).**  Wherever the L-channel strictly dominates
the bridge error (`‖E z‖ < ‖F z‖`), the perturbed pencil `d = -F + E` cannot vanish.
-/
theorem focal_no_zero_of_dominant {F E d : ℂ → ℂ} {S : Set ℂ}
    (hbridge : ∀ z ∈ S, d z = -F z + E z)
    (hdom : ∀ z ∈ S, ‖E z‖ < ‖F z‖) :
    ∀ z ∈ S, d z ≠ 0 := by
  intro z hz; specialize hdom z hz; simp_all +decide;
  rw [ add_eq_zero_iff_eq_neg ] ; aesop

/-
**Explicit location bound.**  At a critical-line simple zero `γ` (`F γ = 0`, `a/2 ≤ F'` on the
window) with bridge error `|E| ≤ ε`, **every** focal zero `Td` of `d = -F + E` in the window
satisfies `|Td - γ| ≤ 2ε/a`.
-/
theorem real_simple_zero_location
    {F E F' : ℝ → ℝ} {γ r a ε : ℝ}
    (ha : 0 < a)
    (hFγ : F γ = 0)
    (hderiv : ∀ t ∈ Icc (γ - r) (γ + r), HasDerivAt F (F' t) t)
    (hF'lb : ∀ t ∈ Icc (γ - r) (γ + r), a / 2 ≤ F' t)
    (hEbound : ∀ t ∈ Icc (γ - r) (γ + r), |E t| ≤ ε)
    {Td : ℝ} (hTd : Td ∈ Icc (γ - r) (γ + r)) (hroot : -(F Td) + E Td = 0) :
    |Td - γ| ≤ 2 * ε / a := by
  have h_cont : ContinuousOn F (Set.Icc (γ - r) (γ + r)) := by
    exact fun t ht => ( hderiv t ht |> HasDerivAt.continuousAt |> ContinuousAt.continuousWithinAt );
  by_cases h_cases : Td ≥ γ;
  · by_cases h_cases : Td = γ;
    · simp [h_cases];
      exact div_nonneg ( mul_nonneg zero_le_two ( le_trans ( abs_nonneg _ ) ( hEbound γ ⟨ by linarith [ hTd.1 ], by linarith [ hTd.2 ] ⟩ ) ) ) ha.le;
    · have := exists_deriv_eq_slope F ( lt_of_le_of_ne ‹_› ( Ne.symm h_cases ) );
      contrapose! this;
      simp +zetaDelta at *;
      exact ⟨ h_cont.mono ( Set.Icc_subset_Icc ( by linarith ) ( by linarith ) ), fun x hx => ( hderiv x ( by linarith [ hx.1 ] ) ( by linarith [ hx.2 ] ) |> HasDerivAt.differentiableAt |> DifferentiableAt.differentiableWithinAt ), fun c hc₁ hc₂ => by rw [ hderiv c ( by linarith ) ( by linarith ) |> HasDerivAt.deriv ] ; rw [ eq_div_iff ] <;> cases abs_cases ( Td - γ ) <;> nlinarith [ hF'lb c ( by linarith ) ( by linarith ), abs_le.mp ( hEbound Td ( by linarith ) ( by linarith ) ), mul_div_cancel₀ ( 2 * ε ) ha.ne' ] ⟩;
  · have := exists_deriv_eq_slope F ( lt_of_not_ge h_cases );
    simp +zetaDelta at *;
    exact this ( h_cont.mono ( Set.Icc_subset_Icc ( by linarith ) ( by linarith ) ) ) ( fun x hx => ( hderiv x ( by linarith [ hx.1 ] ) ( by linarith [ hx.2 ] ) |> HasDerivAt.differentiableAt |> DifferentiableAt.differentiableWithinAt ) ) |> fun ⟨ c, hc₁, hc₂ ⟩ => by rw [ eq_div_iff ] at hc₂ <;> nlinarith [ hF'lb c ( by linarith ) ( by linarith ), abs_of_neg ( by linarith : Td - γ < 0 ), mul_div_cancel₀ ( 2 * ε ) ha.ne', abs_le.mp ( hEbound Td ( by linarith ) ( by linarith ) ), abs_le.mp ( hEbound γ ( by linarith ) ( by linarith ) ), hderiv c ( by linarith ) ( by linarith ) |> HasDerivAt.deriv ] ;

/-
**Existence (with location bound).**  Under the stability gap `ε < a·r/4`, the perturbed
pencil `d = -F + E` has a focal zero `Td` in the open window `(γ - r, γ + r)`, and it satisfies the
location bound `|Td - γ| ≤ 2ε/a`.
-/
theorem real_simple_zero_exists
    {F E F' : ℝ → ℝ} {γ r a ε : ℝ}
    (hr : 0 < r) (ha : 0 < a)
    (hFγ : F γ = 0)
    (hderiv : ∀ t ∈ Icc (γ - r) (γ + r), HasDerivAt F (F' t) t)
    (hF'lb : ∀ t ∈ Icc (γ - r) (γ + r), a / 2 ≤ F' t)
    (hEcont : ContinuousOn E (Icc (γ - r) (γ + r)))
    (hEbound : ∀ t ∈ Icc (γ - r) (γ + r), |E t| ≤ ε)
    (hsmall : ε < a * r / 4) :
    ∃ Td ∈ Ioo (γ - r) (γ + r), (-(F Td) + E Td = 0) ∧ |Td - γ| ≤ 2 * ε / a := by
  have h_signs : -F (γ + r) + E (γ + r) < 0 ∧ -F (γ - r) + E (γ - r) > 0 := by
    constructor;
    · have := exists_deriv_eq_slope F ( show γ < γ + r by linarith );
      contrapose! this;
      exact ⟨ continuousOn_of_forall_continuousAt fun x hx => HasDerivAt.continuousAt ( hderiv x ⟨ by linarith [ hx.1 ], by linarith [ hx.2 ] ⟩ ), fun x hx => ( hderiv x ⟨ by linarith [ hx.1 ], by linarith [ hx.2 ] ⟩ |> HasDerivAt.differentiableAt |> DifferentiableAt.differentiableWithinAt ), fun x hx => by rw [ hderiv x ⟨ by linarith [ hx.1 ], by linarith [ hx.2 ] ⟩ |> HasDerivAt.deriv ] ; rw [ ne_eq, eq_div_iff ] <;> nlinarith [ hF'lb x ⟨ by linarith [ hx.1 ], by linarith [ hx.2 ] ⟩, abs_le.mp ( hEbound ( γ + r ) ⟨ by linarith, by linarith ⟩ ) ] ⟩;
    · by_contra h_contra;
      have := exists_deriv_eq_slope F ( show γ - r < γ by linarith ) ; norm_num at *;
      exact absurd ( this ( by exact continuousOn_of_forall_continuousAt fun t ht => HasDerivAt.continuousAt ( hderiv t ( by linarith [ ht.1 ] ) ( by linarith [ ht.2 ] ) ) ) ( by exact fun t ht => DifferentiableAt.differentiableWithinAt ( hderiv t ( by linarith [ ht.1 ] ) ( by linarith [ ht.2 ] ) |> HasDerivAt.differentiableAt ) ) ) ( by rintro ⟨ c, ⟨ hc₁, hc₂ ⟩, hc ⟩ ; rw [ eq_div_iff ] at hc <;> nlinarith [ hF'lb c ( by linarith ) ( by linarith ), abs_le.mp ( hEbound ( γ - r ) ( by linarith ) ( by linarith ) ), hderiv c ( by linarith ) ( by linarith ) |> HasDerivAt.deriv ] );
  have h_exists_zero : ∃ Td ∈ Set.Ioo (γ - r) (γ + r), -F Td + E Td = 0 := by
    apply_rules [ intermediate_value_Ioo' ] ; linarith;
    exact ContinuousOn.add ( ContinuousOn.neg ( continuousOn_of_forall_continuousAt fun x hx => HasDerivAt.continuousAt ( hderiv x hx ) ) ) hEcont;
  obtain ⟨ Td, hTd₁, hTd₂ ⟩ := h_exists_zero; use Td; refine' ⟨ hTd₁, hTd₂, _ ⟩ ; exact real_simple_zero_location ha hFγ ( fun t ht => hderiv t ht ) ( fun t ht => hF'lb t ht ) ( fun t ht => hEbound t ht ) ( Set.mem_Icc.mpr ⟨ by linarith [ hTd₁.1 ], by linarith [ hTd₁.2 ] ⟩ ) hTd₂;

/-
**Existence & uniqueness.**  Adding the regularity `|E'| < a/2` on the window (the real-line
analogue of analyticity, which makes `d = -F + E` strictly monotone), the focal zero in the open
window is **unique**.
-/
theorem real_simple_zero_unique
    {F E F' E' : ℝ → ℝ} {γ r a ε : ℝ}
    (hr : 0 < r) (ha : 0 < a)
    (hFγ : F γ = 0)
    (hFderiv : ∀ t ∈ Icc (γ - r) (γ + r), HasDerivAt F (F' t) t)
    (hEderiv : ∀ t ∈ Icc (γ - r) (γ + r), HasDerivAt E (E' t) t)
    (hF'lb : ∀ t ∈ Icc (γ - r) (γ + r), a / 2 ≤ F' t)
    (hE'b : ∀ t ∈ Icc (γ - r) (γ + r), |E' t| < a / 2)
    (hEbound : ∀ t ∈ Icc (γ - r) (γ + r), |E t| ≤ ε)
    (hsmall : ε < a * r / 4) :
    ∃! Td : ℝ, Td ∈ Ioo (γ - r) (γ + r) ∧ (-(F Td) + E Td = 0) := by
  -- By the properties of the derivative, we know that $g'(t) = -F'(t) + E'(t)$.
  have h_deriv : ∀ t ∈ Set.Ioo (γ - r) (γ + r), deriv (fun t => -(F t) + E t) t = -(F' t) + E' t := by
    intro t ht; exact HasDerivAt.deriv ( HasDerivAt.add ( HasDerivAt.neg ( hFderiv t <| Set.Ioo_subset_Icc_self ht ) ) ( hEderiv t <| Set.Ioo_subset_Icc_self ht ) ) ;
  obtain ⟨Td, hTd⟩ : ∃ Td ∈ Set.Ioo (γ - r) (γ + r), -(F Td) + E Td = 0 := by
    obtain ⟨Td, hTd⟩ : ∃ Td ∈ Set.Ioo (γ - r) (γ + r), (-(F Td) + E Td = 0) ∧ |Td - γ| ≤ 2 * ε / a := by
      apply_rules [ real_simple_zero_exists ];
      exact fun t ht => ( hEderiv t ht |> HasDerivAt.continuousAt |> ContinuousAt.continuousWithinAt );
    exact ⟨ Td, hTd.1, hTd.2.1 ⟩;
  refine' ⟨ Td, hTd, fun t ht => _ ⟩;
  have h_unique : StrictAntiOn (fun t => -(F t) + E t) (Set.Icc (γ - r) (γ + r)) := by
    apply_rules [ strictAntiOn_of_deriv_neg ];
    · exact convex_Icc _ _;
    · exact ContinuousOn.add ( ContinuousOn.neg ( continuousOn_of_forall_continuousAt fun x hx => HasDerivAt.continuousAt ( hFderiv x hx ) ) ) ( continuousOn_of_forall_continuousAt fun x hx => HasDerivAt.continuousAt ( hEderiv x hx ) );
    · simp +zetaDelta at *;
      grind;
  exact StrictAntiOn.injOn h_unique ( Set.Ioo_subset_Icc_self ht.1 ) ( Set.Ioo_subset_Icc_self hTd.1 ) ( by linarith [ ht.2, hTd.2 ] )

end CriticalLinePhasor.Admissible