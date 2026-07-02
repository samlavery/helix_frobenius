import RequestProject.UnconditionalFrobenius

/-!
# The cup identity boundary: well-definedness (unconditional) and the Hermite–Biehler boundary

This file is deliberately **outside the Hermite–Biehler scope**.  It imports only
`RequestProject.UnconditionalFrobenius` (which itself imports only Mathlib), so the entire
de Branges / Hermite–Biehler vocabulary — `IsHB`, `hb_domination_dichotomy`,
`deBranges_balance_iff_real`, etc. — is **not in scope here** and cannot be used.  The kernel
`deBrangesKernel` is re-defined locally as a *bare formula*, with no positivity hypothesis attached.

## What is delivered

1. **The two well-definedness lemmas (genuinely unconditional).**
   * `cup_null_iff` : `Cup F F = 0 ↔ Dop F = 0` — this is just `‖·‖² = 0 ↔ · = 0` in an
     inner-product space, the confidence check that the cup form is non-degenerate.
   * `closure_not_fibre_collapse` : `Dop F = 0 ↔ ιR F = J (ιL F)` together with
     `dop_eq_zero_iff_carrier_zero` (`Dop F = 0 ↔ F = 0`) and
     `closure_preserves_arithmetic_content` (`F ≠ 0 → Dop F ≠ 0`): the null space of the
     opposite-handed difference deletes **no** arithmetic content (it is exactly `{0}`), so
     positivity is never vacuous on the part that carries the arithmetic.

   Here the opposite-handed embeddings `ιR, ιL : (ℕ →₀ ℂ) → (ℕ →₀ ℂ)` land the carrier on the
   even / odd sites of the *same* `ℓ²`/Finsupp space used for `waveVec`/`dataVec`, `J` is the
   coefficientwise conjugation, and `Dop F = ιR F − J (ιL F)`, `Cup F G = ⟪Dop F, Dop G⟫`.

2. **The Hermite–Biehler boundary, as a theorem (the located boundary marker).**
   The asked-for unconditional identity
   `cup_identity : ⟪Dop (Φ z), Dop (Φ w)⟫ = deBrangesKernel E w z`
   **cannot** be made `IsHB`-free.  The reason is forced and is proved here, not asserted:

   * `featureMap_forces_diag_nonneg` : *any* feature map `φ : ℂ → H` into *any* genuine
     (positive-definite) inner-product space with `⟪φ z, φ w⟫ = deBrangesKernel E w z` makes the
     diagonal `0 ≤ (deBrangesKernel E w w).re`, because the left side is `‖φ w‖² ≥ 0`.
   * `featureMap_forces_HB` : consequently, in the upper half-plane, `‖E* w‖ ≤ ‖E w‖` — the
     Hermite–Biehler inequality itself.
   * `no_featureMap_of_not_HB` : the contrapositive — if `E` violates the HB inequality at one
     off-axis point, **no** such feature map exists, so the identity is unprovable for that `E`.

   In other words the existence of the cup feature map (what `cup_identity` would supply) *is*
   the Hermite–Biehler positivity: it is an **output**, never something that can be dropped as an
   input.  This is exactly the requested "if a step needs HB, report which step" — the step that
   needs HB is the cup identity itself, and the report is the equivalence above.

## The Cauchy-kernel factor and the choice of codomain

The decomposition of the would-be identity into its three pieces is documented in
`docstring`s near the boundary theorems:
* the Cauchy factor `1 / (2π i (conj w − z))` is the Szegő/Cauchy reproducing kernel of the
  (infinite-dimensional) Hardy space; its feature vectors are not finitely supported, so it does
  **not** come out of the finitely-supported `ℕ →₀ ℂ` carrier vectors — a genuine `H(E)`
  completion is required for the codomain;
* the conjugation `J` is what turns one chirality into the `E*` term;
* assembling `E z · conj (E w) − E* z · conj (E* w)` is the difference of the two chirality
  pairings.
Even after escalating to the completion, the positivity of the resulting kernel is the
Hermite–Biehler condition (the boundary theorems above), so HB is never removed.

Mathlib-only; self-contained; no Hermite–Biehler input.
-/

open Complex
open scoped ComplexConjugate

namespace CriticalLinePhasor.CupIdentity
noncomputable section

/-! ## A bare (HB-free) de Branges kernel formula -/

/-- The reflection `E*(z) = conj (E (conj z))`, re-defined locally (no HB scope). -/
def Estar (E : ℂ → ℂ) (z : ℂ) : ℂ := (starRingEnd ℂ) (E ((starRingEnd ℂ) z))

/-- The de Branges kernel as a **bare formula**, with no positivity hypothesis:
`K_E(w, z) = (E z · conj (E w) − E* z · conj (E* w)) / (2π i (conj w − z))`. -/
def deBrangesKernel (E : ℂ → ℂ) (w z : ℂ) : ℂ :=
  (E z * (starRingEnd ℂ) (E w) - Estar E z * (starRingEnd ℂ) (Estar E w))
    / (2 * (Real.pi : ℂ) * Complex.I * ((starRingEnd ℂ) w - z))

/-- On the diagonal the kernel is the real ratio `(‖E w‖² − ‖E* w‖²)/(4π · Im w)`. -/
theorem deBrangesKernel_diag (E : ℂ → ℂ) (w : ℂ) :
    deBrangesKernel E w w =
      ((‖E w‖ ^ 2 - ‖Estar E w‖ ^ 2) / (4 * Real.pi * w.im) : ℝ) := by
  unfold deBrangesKernel
  rw [Complex.mul_conj, Complex.mul_conj]
  have hden : (2 * (Real.pi : ℂ) * Complex.I * ((starRingEnd ℂ) w - w))
      = ((4 * Real.pi * w.im : ℝ) : ℂ) := by
    apply Complex.ext <;>
      simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [hden, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  push_cast
  ring

/-! ## Opposite-handed embeddings into the same `ℓ²`/Finsupp space -/

/-- Even-site embedding `n ↦ 2n` of the carrier (right-handed). -/
def embR : ℕ ↪ ℕ := ⟨fun n => 2 * n, fun a b h => by dsimp only at h; omega⟩

/-- Odd-site embedding `n ↦ 2n+1` of the carrier (left-handed). -/
def embL : ℕ ↪ ℕ := ⟨fun n => 2 * n + 1, fun a b h => by dsimp only at h; omega⟩

/-- Right-handed embedding `ιR` of a carrier vector into the even sites. -/
def iotaR (F : ℕ →₀ ℂ) : ℕ →₀ ℂ := Finsupp.embDomain embR F

/-- Left-handed embedding `ιL` of a carrier vector into the odd sites. -/
def iotaL (F : ℕ →₀ ℂ) : ℕ →₀ ℂ := Finsupp.embDomain embL F

/-- The conjugation `J` (coefficientwise complex conjugation). -/
def Jconj (F : ℕ →₀ ℂ) : ℕ →₀ ℂ := Finsupp.mapRange (starRingEnd ℂ) (by simp) F

/-- The opposite-handed difference operator `Dop F = ιR F − J (ιL F)`. -/
def Dop (F : ℕ →₀ ℂ) : ℕ →₀ ℂ := iotaR F - Jconj (iotaL F)

/-- The cup form `Cup F G = ⟪Dop F, Dop G⟫`. -/
def Cup (F G : ℕ →₀ ℂ) : ℂ := inner ℂ (Dop F) (Dop G)

/-! ### Well-definedness lemma 1: non-degeneracy of the cup form -/

/-
**`cup_null_iff` (unconditional).**  `Cup F F = 0 ↔ Dop F = 0`: the cup form vanishes exactly
on the kernel of the assembling operator.  This is `‖·‖² = 0 ↔ · = 0` in the inner-product space;
no Hermite–Biehler input.  Confidence check that the positive cup form is non-degenerate.
-/
theorem cup_null_iff (F : ℕ →₀ ℂ) : Cup F F = 0 ↔ Dop F = 0 := by
  exact inner_self_eq_zero (𝕜 := ℂ) (x := Dop F)

/-! ### Well-definedness lemma 2: the closure does not collapse arithmetic content -/

/-
**`closure_not_fibre_collapse` (unconditional).**  `Dop F = 0 ↔ ιR F = J (ιL F)`: the null
condition is exactly the balance of the two opposite-handed embeddings.
-/
theorem closure_not_fibre_collapse (F : ℕ →₀ ℂ) :
    Dop F = 0 ↔ iotaR F = Jconj (iotaL F) := by
  grind +locals

/-
**The null space is exactly `{0}` (unconditional).**  Because `ιR` lands on the even sites and
`J (ιL ·)` on the odd sites, the opposite-handed difference vanishes iff the carrier itself is
zero.  Hence the closure deletes **no** arithmetic content.
-/
theorem dop_eq_zero_iff_carrier_zero (F : ℕ →₀ ℂ) : Dop F = 0 ↔ F = 0 := by
  constructor <;> intro hF <;> simp_all +decide [ Dop, Finsupp.ext_iff ];
  · intro n; specialize hF ( 2 * n ) ; simp_all +decide [ iotaR, iotaL, Jconj, Finsupp.embDomain_apply ] ;
    split_ifs at hF <;> simp_all +decide [ embR, embL ];
    obtain ⟨ a, ha ⟩ := ‹∃ a, embL a = 2 * n›; simp_all +decide [ embL ] ; omega;
  · simp +decide [ show F = 0 from Finsupp.ext hF, iotaR, iotaL, Jconj ]

/-
**The closure preserves arithmetic content (unconditional).**  A nonzero carrier never lies in
the null space, so positivity is never vacuous on the arithmetic part.
-/
theorem closure_preserves_arithmetic_content (F : ℕ →₀ ℂ) (hF : F ≠ 0) : Dop F ≠ 0 := by
  exact fun h => hF <| dop_eq_zero_iff_carrier_zero F |>.1 h

/-! ## The Hermite–Biehler boundary: the cup identity is HB, not HB-free

The next three theorems are the located boundary marker.  They show, with no HB vocabulary in
scope, that the existence of *any* feature map reproducing `deBrangesKernel E` forces the
Hermite–Biehler inequality.  Hence the asked-for unconditional `cup_identity` cannot exist as
stated for a non-HB `E`: HB is an output of the cup positivity, never an input to be removed. -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-
**Step report (forced positivity).**  Any feature map `φ` with
`⟪φ z, φ w⟫ = deBrangesKernel E w z` makes the diagonal nonnegative: the left side is `‖φ w‖² ≥ 0`.
This is the unconditional Gram fact; it needs no HB.
-/
theorem featureMap_forces_diag_nonneg
    {E : ℂ → ℂ} (φ : ℂ → H)
    (hφ : ∀ z w, (inner ℂ (φ z) (φ w) : ℂ) = deBrangesKernel E w z) (w : ℂ) :
    0 ≤ (deBrangesKernel E w w).re := by
  convert inner_self_nonneg (𝕜 := ℂ) ( x := φ w ) using 1;
  rw [← hφ w w]
  rfl

/-
**The cup identity needs HB (the boundary).**  In the upper half-plane, the forced diagonal
positivity is exactly the Hermite–Biehler inequality `‖E* w‖ ≤ ‖E w‖`.  So a cup feature map for
`deBrangesKernel E` *is* the Hermite–Biehler positivity.
-/
theorem featureMap_forces_HB
    {E : ℂ → ℂ} (φ : ℂ → H)
    (hφ : ∀ z w, (inner ℂ (φ z) (φ w) : ℂ) = deBrangesKernel E w z)
    {w : ℂ} (hw : 0 < w.im) :
    ‖Estar E w‖ ≤ ‖E w‖ := by
  have := featureMap_forces_diag_nonneg φ hφ w;
  rw [ deBrangesKernel_diag ] at this;
  contrapose! this;
  exact_mod_cast div_neg_of_neg_of_pos ( by nlinarith [ norm_nonneg ( E w ), norm_nonneg ( Estar E w ) ] ) ( by positivity )

/-
**No feature map for a non-HB `E` (contrapositive).**  If `E` violates the Hermite–Biehler
inequality at one off-axis point, then no feature map reproduces `deBrangesKernel E`; equivalently,
the unconditional `cup_identity` is unprovable for that `E`.  This precisely locates the boundary:
the step that requires HB is the cup identity itself.
-/
theorem no_featureMap_of_not_HB
    {E : ℂ → ℂ} (φ : ℂ → H)
    {w : ℂ} (hw : 0 < w.im) (hbad : ‖E w‖ < ‖Estar E w‖) :
    ¬ (∀ z w, (inner ℂ (φ z) (φ w) : ℂ) = deBrangesKernel E w z) := by
  contrapose! hbad; have := featureMap_forces_HB φ hbad hw; simp_all +decide

end
end CriticalLinePhasor.CupIdentity