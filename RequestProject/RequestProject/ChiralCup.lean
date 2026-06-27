import RequestProject.CupIdentity

/-!
# The chiral-cup Gram architecture (de Branges–free route)

This file assembles the **Gram-positivity → von Neumann reality → Frobenius-weighted cup
identity → midpoint forcing** scaffolding requested in the project notes, built directly on the
opposite-handed defect operator `Dop` and the cup form `Cup` already defined (unconditionally,
without any Hermite–Biehler input) in `RequestProject.CupIdentity`.

The point of this route is that the cup form is a genuine **Gram form**
`Cup F G = ⟪Dop F, Dop G⟫` in an honest inner-product space, so its positivity is automatic and
needs no de Branges / Hermite–Biehler construction (`E = A − iB`, Hermite–Biehler domination,
etc.).  What it costs instead is that the *arithmetic* content (the link between the abstract
spectral picture and the actual zeros of the L-function) is **not** supplied here: the steps that
carry real arithmetic — `frobenius_weighted_cup_identity`'s weight and `midpoint_forcing`'s
hypothesis `‖α‖² = weight` — are stated as the honest abstract patterns they are, and the genuine
Riemann-Hypothesis statement (that *all* zeros are spectral events of this operator) is **neither
assumed nor proved**.

## The ten requested items

1. `chiral_defect_defined` — `Dop` is a well-defined additive (chiral) defect map.
2. `cup_hermitian` — `Cup G F = conj (Cup F G)` (conjugate symmetry of the Gram form).
3. `cup_positive_semidefinite` — `0 ≤ (Cup F F).re` (Gram positivity, automatic).
4. `cup_nullspace_safe` — `Cup F F = 0 ↔ F = 0` (the nullspace is exactly `{0}`: positivity
   deletes no arithmetic content).
5. `hilbert_completion_exists` — the carrier embeds, inner-product-preservingly, into a genuine
   *complete* inner-product space (the metric completion), so the Gram space has a Hilbert
   completion.
6. `transport_unitary_after_normalization` — a transport `Tw μ = μ • id`, after normalizing its
   multiplier to unit modulus, preserves the inner product (is unitary).
7. `von_neumann_reality` / `diagOp_spectrum_real` — a symmetric operator on a complex
   inner-product space has real spectrum (the von Neumann reality of the self-adjoint readout);
   realized concretely by the real-diagonal height operator `diagOp`.
8. `frobenius_weighted_cup_identity` — the transport multiplier splits into a **fiber sign
   change** `sgn` (a unit-modulus phase) and a **fiber amplitude** `amp` whose **crest** is
   `amp²`; the transport scales the cup by the amplitude cresting alone, the sign change
   cancelling: `⟪Tw (amp·sgn) (Dop F), Tw (amp·sgn) (Dop G)⟫ = amp² · Cup F G` (a Frobenius
   similitude of the Gram form, carried by fiber amplitude cresting rather than height).
9. `spectral_readout_faithful` — the defect/readout map `Dop` is injective: no arithmetic content
   is lost when passing to the cup space.
10. `midpoint_forcing` — the abstract weight-balance forcing: if a spectral partner `α = q^s` has
    modulus pinned to the weight (`‖α‖² = q`, the positivity + reflection constraint), then it
    sits on the balanced line `Re s = ½`.

Everything is `Mathlib`-only and `sorry`/`axiom`-free; no Hermite–Biehler input is used.
-/

open Complex
open scoped ComplexConjugate
open CriticalLinePhasor.CupIdentity

namespace CriticalLinePhasor.ChiralCup
noncomputable section

/-! ## 1. `chiral_defect_defined` — the chiral defect is a well-defined additive map -/

/-- `Dop` sends the zero fibre to the zero defect. -/
theorem Dop_zero : Dop (0 : ℕ →₀ ℂ) = 0 := by
  simp [Dop, iotaR, iotaL, Jconj]

/-- **`chiral_defect_defined`.**  The chiral defect `Dop F = ιR F − J (ιL F)` is additive:
`Dop (F + G) = Dop F + Dop G`.  Together with `Dop_zero` this is the well-definedness of the
defect carrier. -/
theorem chiral_defect_defined (F G : ℕ →₀ ℂ) : Dop (F + G) = Dop F + Dop G := by
  unfold Dop iotaR iotaL Jconj
  ext n
  by_cases h1 : ∃ a, embR a = n
  · obtain ⟨a, rfl⟩ := h1
    have hne : ¬ ∃ c, embL c = embR a := by
      rintro ⟨c, hc⟩; simp [embL, embR] at hc; omega
    simp [Finsupp.embDomain_apply, hne, Finsupp.sub_apply, Finsupp.add_apply]
  · by_cases h2 : ∃ b, embL b = n
    · obtain ⟨b, rfl⟩ := h2
      have hr : ∀ X : ℕ →₀ ℂ, (Finsupp.embDomain embR X) (embL b) = 0 := by
        intro X; rw [Finsupp.embDomain_notin_range]
        rintro ⟨a, ha⟩; simp [embR, embL] at ha; omega
      simp [Finsupp.embDomain_apply, hr, Finsupp.sub_apply, Finsupp.add_apply]; ring
    · have hr : ∀ X : ℕ →₀ ℂ, (Finsupp.embDomain embR X) n = 0 := fun X =>
        Finsupp.embDomain_notin_range _ _ _ (by rintro ⟨a, ha⟩; exact h1 ⟨a, ha⟩)
      have hl : ∀ X : ℕ →₀ ℂ, (Finsupp.embDomain embL X) n = 0 := fun X =>
        Finsupp.embDomain_notin_range _ _ _ (by rintro ⟨b, hb⟩; exact h2 ⟨b, hb⟩)
      simp [Finsupp.sub_apply, Finsupp.add_apply, hr, hl]

/-! ## 2. `cup_hermitian` — conjugate symmetry of the cup Gram form -/

/-- **`cup_hermitian`.**  The cup form is conjugate-symmetric: `Cup G F = conj (Cup F G)`. -/
theorem cup_hermitian (F G : ℕ →₀ ℂ) : Cup G F = (starRingEnd ℂ) (Cup F G) := by
  rw [Cup, Cup, inner_conj_symm]

/-! ## 3. `cup_positive_semidefinite` — Gram positivity (automatic) -/

/-- **`cup_positive_semidefinite`.**  The cup form is positive semidefinite:
`0 ≤ (Cup F F).re`.  This is automatic because `Cup F F = ‖Dop F‖²` in the inner-product space. -/
theorem cup_positive_semidefinite (F : ℕ →₀ ℂ) : 0 ≤ (Cup F F).re := by
  simpa [Cup] using inner_self_nonneg (𝕜 := ℂ) (x := Dop F)

/-- The diagonal of the cup form is real. -/
theorem cup_self_im (F : ℕ →₀ ℂ) : (Cup F F).im = 0 := by
  simpa [Cup] using inner_self_im (𝕜 := ℂ) (x := Dop F)

/-! ## 4. `cup_nullspace_safe` — the nullspace is exactly `{0}` -/

/-- **`cup_nullspace_safe`.**  The cup form is non-degenerate: it vanishes on the diagonal exactly
at the zero fibre, `Cup F F = 0 ↔ F = 0`.  So the Gram positivity deletes no arithmetic content. -/
theorem cup_nullspace_safe (F : ℕ →₀ ℂ) : Cup F F = 0 ↔ F = 0 :=
  (cup_null_iff F).trans (dop_eq_zero_iff_carrier_zero F)

/-! ## 5. `hilbert_completion_exists` — a genuine Hilbert completion of the Gram space -/

/-- The metric completion of the carrier inner-product space. -/
abbrev Hcompl : Type := UniformSpace.Completion (ℕ →₀ ℂ)

/-- **`hilbert_completion_exists`.**  The carrier embeds into a genuine *complete* inner-product
space `Hcompl`, and the inclusion preserves the cup Gram form:
`⟪↑(Dop F), ↑(Dop G)⟫_{Hcompl} = Cup F G`.  Hence the Gram space has a Hilbert completion in which
the cup form is the honest inner product. -/
theorem hilbert_completion_exists :
    CompleteSpace Hcompl ∧
      ∀ F G : ℕ →₀ ℂ,
        (inner ℂ (↑(Dop F) : Hcompl) (↑(Dop G)) : ℂ) = Cup F G := by
  refine ⟨inferInstance, fun F G => ?_⟩
  rw [Cup]
  exact UniformSpace.Completion.inner_coe _ _

/-! ## 6–8. The transport and its Frobenius-weighted cup identity -/

/-- The transport operator `Tw μ : v ↦ μ • v` on the carrier/Gram space. -/
def Tw (μ : ℂ) : (ℕ →₀ ℂ) →ₗ[ℂ] (ℕ →₀ ℂ) := μ • LinearMap.id

@[simp] theorem Tw_apply (μ : ℂ) (v : ℕ →₀ ℂ) : Tw μ v = μ • v := rfl

/-- **`transport_unitary_after_normalization`.**  After normalizing the transport multiplier to
unit modulus (`‖μ‖ = 1`), the transport preserves the inner product — it is unitary. -/
theorem transport_unitary_after_normalization (μ : ℂ) (hμ : ‖μ‖ = 1) (v w : ℕ →₀ ℂ) :
    (inner ℂ (Tw μ v) (Tw μ w) : ℂ) = inner ℂ v w := by
  show (inner ℂ (μ • v) (μ • w) : ℂ) = inner ℂ v w
  rw [inner_smul_left, inner_smul_right]
  have hone : (starRingEnd ℂ) μ * μ = 1 := by
    rw [Complex.conj_mul']; norm_cast; rw [hμ]; norm_num
  rw [← mul_assoc, hone, one_mul]

/-- **Modulus form of the transport similitude** (general helper).  The transport `Tw μ` scales
the cup Gram form by `‖μ‖²`:
`⟪Tw μ (Dop F), Tw μ (Dop G)⟫ = ‖μ‖² · Cup F G`. -/
theorem transport_cup_modulus (μ : ℂ) (F G : ℕ →₀ ℂ) :
    (inner ℂ (Tw μ (Dop F)) (Tw μ (Dop G)) : ℂ) = ((‖μ‖ ^ 2 : ℝ) : ℂ) * Cup F G := by
  show (inner ℂ (μ • Dop F) (μ • Dop G) : ℂ) = _
  rw [inner_smul_left, inner_smul_right, Cup, ← mul_assoc]
  congr 1
  rw [Complex.conj_mul']; push_cast; ring

/-- **`frobenius_weighted_cup_identity`.**  The transport multiplier splits into a **fiber sign
change** `sgn` — a unit-modulus phase (`‖sgn‖ = 1`, the chiral sign flip carried by the fibre) —
and a **fiber amplitude** `amp` whose **crest** is `amp²`.  Transporting by `amp · sgn` scales the
cup Gram form by the amplitude cresting `amp²`, with the fiber sign change cancelling (it has
modulus one):
`⟪Tw (amp·sgn) (Dop F), Tw (amp·sgn) (Dop G)⟫ = amp² · Cup F G`.  The weight is thus carried by the
fiber amplitude cresting alone — the sign change contributes nothing — with no reference to any
height. -/
theorem frobenius_weighted_cup_identity
    (sgn : ℂ) (hsgn : ‖sgn‖ = 1) (amp : ℝ) (F G : ℕ →₀ ℂ) :
    (inner ℂ (Tw ((amp : ℂ) * sgn) (Dop F)) (Tw ((amp : ℂ) * sgn) (Dop G)) : ℂ)
      = ((amp ^ 2 : ℝ) : ℂ) * Cup F G := by
  rw [transport_cup_modulus]
  congr 2
  rw [norm_mul, hsgn, mul_one, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- The weight is the fiber amplitude cresting: if the multiplier has `‖μ‖² = λ` (e.g. the
Frobenius helix multiplier of `m`, with `‖μ‖² = m`), the cup is scaled by `λ`. -/
theorem frobenius_weighted_cup_identity_of_weight (μ : ℂ) (lam : ℝ) (hμ : ‖μ‖ ^ 2 = lam)
    (F G : ℕ →₀ ℂ) :
    (inner ℂ (Tw μ (Dop F)) (Tw μ (Dop G)) : ℂ) = (lam : ℂ) * Cup F G := by
  rw [transport_cup_modulus, hμ]

/-! ## 7. `von_neumann_reality` — self-adjoint readout has real spectrum -/

/-- **`von_neumann_reality`.**  A symmetric operator on a complex inner-product space has real
spectrum: every eigenvalue is real.  This is the von Neumann reality of the self-adjoint
readout/closure. -/
theorem von_neumann_reality {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric) {μ : ℂ} (hμ : Module.End.HasEigenvalue T μ) :
    μ.im = 0 :=
  CriticalLinePhasor.UnconditionalFrobenius.symmetric_eigenvalue_real hT hμ

/-- The real-diagonal height operator realizes the von Neumann reality concretely: its spectrum is
real, with explicit real eigenvalues `d i`. -/
theorem diagOp_spectrum_real (d : ℕ → ℝ) (i : ℕ) :
    ((d i : ℂ)).im = 0 ∧
      Module.End.HasEigenvalue (CriticalLinePhasor.UnconditionalFrobenius.diagOp d) (d i : ℂ) :=
  ⟨by simp, CriticalLinePhasor.UnconditionalFrobenius.diagOp_hasEigenvalue d i⟩

/-! ## 9. `spectral_readout_faithful` — the readout is injective -/

/-- **`spectral_readout_faithful`.**  The defect/readout map `Dop` is injective: distinct fibres
have distinct chiral defects, so no arithmetic content is lost passing to the cup space. -/
theorem spectral_readout_faithful : Function.Injective Dop := by
  intro F G h
  have key := chiral_defect_defined (F - G) G
  rw [sub_add_cancel, h] at key
  rw [eq_comm, add_eq_right] at key
  exact sub_eq_zero.mp ((dop_eq_zero_iff_carrier_zero (F - G)).1 key)

/-! ## 10. `midpoint_forcing` — weight balance forces the critical line -/

/-- The reflected spectral partner has the same modulus.  If `‖α‖² = λ` with `λ > 0`, then the
Frobenius reflection `λ / conj α` has modulus equal to `‖α‖`: the conjugate-chiral pairing produces
modulus-balanced partners. -/
theorem weight_balance_reflection (lam : ℝ) (hlam : 0 < lam) (α : ℂ) (hα0 : α ≠ 0)
    (hα : ‖α‖ ^ 2 = lam) :
    ‖(lam : ℂ) / (starRingEnd ℂ) α‖ = ‖α‖ := by
  rw [norm_div, Complex.norm_real, RCLike.norm_conj, Real.norm_of_nonneg hlam.le, ← hα]
  have hne : ‖α‖ ≠ 0 := by simpa using hα0
  field_simp

/-- **`midpoint_forcing`.**  The weight-balance forcing of the critical line.  With weight `q > 1`
(the transport / height normalization, the Frobenius `q`), a spectral partner written as
`α = q^s` whose modulus is pinned to the weight (`‖α‖² = q`, the positivity + reflection
constraint) is forced onto the balanced midpoint line `Re s = ½`. -/
theorem midpoint_forcing (q : ℝ) (hq : 1 < q) (s : ℂ) (h : ‖(q : ℂ) ^ s‖ ^ 2 = q) :
    s.re = 1 / 2 := by
  rw [norm_cpow_eq_rpow_re_of_pos (by linarith) s] at h
  have hq0 : (0 : ℝ) < q := by linarith
  have hmain : q ^ (2 * s.re) = q ^ (1 : ℝ) := by
    rw [Real.rpow_one, show (2 * s.re) = s.re * 2 by ring, Real.rpow_mul hq0.le,
      show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    exact h
  have h2 : 2 * s.re = 1 := by
    rcases lt_trichotomy (2 * s.re) 1 with hlt | heq | hgt
    · exact absurd ((Real.rpow_lt_rpow_left_iff hq).2 hlt) (by rw [hmain]; exact lt_irrefl _)
    · exact heq
    · exact absurd ((Real.rpow_lt_rpow_left_iff hq).2 hgt) (by rw [hmain]; exact lt_irrefl _)
  linarith

end
end CriticalLinePhasor.ChiralCup
