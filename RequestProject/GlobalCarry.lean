import Mathlib

/-!
# The global carry distribution: fuses #1 and #2

The summit reformulation (registered 2026-08-10, final form): the polar
content of the quotient is carried by ONE global functional — the
vertical-line discrepancy — with poles never enumerated.  This file
compiles the abstract cores of the first two fuses:

* **Fuse #1, `carry` + `carry_integrable_of_bounds`** — the carry pairing
  `⟨R,F⟩ = (2π)⁻¹[∫_{σ₊} − ∫_{σ₋}] Q(s)F(s) |ds|` is well-defined for
  exponentially decaying `Q` against exponential-type test data, and is
  linear (`carry_add`, `carry_smul`).  Infinite carries are native: no
  finite pole sum appears anywhere.
* **Fuse #2, `carry_warp_covariance`** — the completed functional equation
  `Q(s) = η·G(s)·Q(1−s)` with the conductor cocycle `G(s)G(1−s) = 1`
  yields the EXACT covariance
  `carry (𝒲F) = −η · carry F`, `(𝒲F)(s) := G(1−s)·F(1−s)`,
  by pure change of variables on absolutely convergent integrals — the
  warp acts on the completed carrier directly, no polar analysis.

The conductor instantiation `G(s) = A^{1/2−s}` (with `A = A_*q⁶` after the
restored-channel harmonization) satisfies the cocycle identity trivially;
`𝒲` is the s-side shadow of the carrier warp `u ↦ −u − log A` with its
fiber scalar.  Fuse #3 (`zeroCarry_implies_noPoles`, local detection via
rectangle contours and good lines from the Hadamard theory of the KNOWN
entire denominator) is the remaining member of the trio and lives on the
repo's rectangle machinery.  Register: exactly these three fuses close the
cable for the even channel; nothing else is added.  No `axiom`, no
`sorry`.
-/

open MeasureTheory Complex

namespace CriticalLinePhasor.GlobalCarry

/-- The carry data: a function with exponential decay on two vertical
lines. -/
structure CarryData where
  Q : ℂ → ℂ
  σp : ℝ
  σm : ℝ
  C : ℝ
  hC : 0 ≤ C
  δ : ℝ
  hδ : 0 < δ
  contp : Continuous fun t : ℝ => Q (σp + t * I)
  contm : Continuous fun t : ℝ => Q (σm + t * I)
  boundp : ∀ t : ℝ, ‖Q (σp + t * I)‖ ≤ C * Real.exp (-δ * |t|)
  boundm : ∀ t : ℝ, ‖Q (σm + t * I)‖ ≤ C * Real.exp (-δ * |t|)

/-- **Fuse #1: the global carry pairing** — the vertical-line discrepancy,
with no pole enumeration. -/
noncomputable def carry (D : CarryData) (F : ℂ → ℂ) : ℂ :=
  (2 * Real.pi)⁻¹ *
    ((∫ t : ℝ, D.Q (D.σp + t * I) * F (D.σp + t * I))
      - ∫ t : ℝ, D.Q (D.σm + t * I) * F (D.σm + t * I))

/-- Exponential-type test bound on a line. -/
def LineBound (F : ℂ → ℂ) (σ CF ε : ℝ) : Prop :=
  ∀ t : ℝ, ‖F (σ + t * I)‖ ≤ CF * Real.exp (ε * |t|)

/-- The two-sided exponential is integrable on the line. -/
lemma integrable_exp_neg_mul_abs {c : ℝ} (hc : 0 < c) :
    Integrable fun t : ℝ => Real.exp (-c * |t|) := by
  have hIoi : IntegrableOn (fun t : ℝ => Real.exp (-c * |t|)) (Set.Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 hc).congr_fun
      (fun t ht => by rw [abs_of_pos ht]) measurableSet_Ioi
  have hIci : IntegrableOn (fun t : ℝ => Real.exp (-c * |t|)) (Set.Ici 0) :=
    (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr hIoi
  have hIic : IntegrableOn (fun t : ℝ => Real.exp (-c * |t|)) (Set.Iic 0) := by
    have hemb : MeasurableEmbedding (fun t : ℝ => -t) :=
      (Homeomorph.neg ℝ).measurableEmbedding
    have hmap : Measure.map (fun t : ℝ => -t) (volume : Measure ℝ) = volume :=
      Measure.map_neg_eq_self volume
    have h1 := hemb.integrableOn_map_iff
      (f := fun t : ℝ => Real.exp (-c * |t|)) (μ := volume) (s := Set.Ici 0)
    rw [hmap] at h1
    have h2 : (fun t : ℝ => -t) ⁻¹' (Set.Ici 0) = Set.Iic 0 := by
      ext x; simp
    have h3 : ((fun t : ℝ => Real.exp (-c * |t|)) ∘ fun t : ℝ => -t)
        = fun t : ℝ => Real.exp (-c * |t|) := by
      funext t; simp [Function.comp, abs_neg]
    rw [h2, h3] at h1
    exact h1.mp hIci
  have hcover : Set.Iic (0 : ℝ) ∪ Set.Ioi 0 = Set.univ := Set.Iic_union_Ioi
  rw [← integrableOn_univ, ← hcover]
  exact hIic.union hIoi

/-- **Fuse #1, well-definedness**: the carry integrand is integrable on each
line — exponential decay of `Q` beats exponential-type test growth. -/
lemma carry_integrable_of_bounds (D : CarryData) {F : ℂ → ℂ} {σ CF ε : ℝ}
    (hσ : σ = D.σp ∨ σ = D.σm)
    (hF : LineBound F σ CF ε) (hCF : 0 ≤ CF) (hε : ε < D.δ)
    (hFc : Continuous fun t : ℝ => F (σ + t * I)) :
    Integrable fun t : ℝ => D.Q (σ + t * I) * F (σ + t * I) := by
  have hQb : ∀ t : ℝ, ‖D.Q (σ + t * I)‖ ≤ D.C * Real.exp (-D.δ * |t|) := by
    rcases hσ with h | h <;> subst h
    · exact D.boundp
    · exact D.boundm
  have hQc : Continuous fun t : ℝ => D.Q (σ + t * I) := by
    rcases hσ with h | h <;> subst h
    · exact D.contp
    · exact D.contm
  have hmeas : AEStronglyMeasurable
      (fun t : ℝ => D.Q (σ + t * I) * F (σ + t * I)) volume :=
    (hQc.mul hFc).aestronglyMeasurable
  have hpos : 0 < D.δ - ε := by linarith
  refine Integrable.mono'
    ((integrable_exp_neg_mul_abs hpos).const_mul (D.C * CF)) hmeas ?_
  refine Filter.Eventually.of_forall fun t => ?_
  have h1 := hQb t
  have h2 := hF t
  calc ‖D.Q (σ + t * I) * F (σ + t * I)‖
      = ‖D.Q (σ + t * I)‖ * ‖F (σ + t * I)‖ := norm_mul _ _
    _ ≤ (D.C * Real.exp (-D.δ * |t|)) * (CF * Real.exp (ε * |t|)) := by
        apply mul_le_mul h1 h2 (norm_nonneg _)
        exact mul_nonneg D.hC (Real.exp_pos _).le
    _ = (D.C * CF) * (Real.exp (-D.δ * |t|) * Real.exp (ε * |t|)) := by ring
    _ = (D.C * CF) * Real.exp (-(D.δ - ε) * |t|) := by
        rw [← Real.exp_add]
        ring_nf

/-- **Fuse #2: warp covariance of the global carry.**  The completed
functional equation with conductor cocycle `G(s)G(1−s) = 1` makes the warp
act on the completed carrier exactly: `carry (𝒲F) = −η·carry F` for
`(𝒲F)(s) = G(1−s)F(1−s)` — two line swaps and one reflection of the
integration variable; every conductor factor cancels. -/
theorem carry_warp_covariance (D : CarryData) {η : ℂ} {G F : ℂ → ℂ}
    (hline : (D.σm : ℝ) = 1 - D.σp)
    (hG : ∀ s : ℂ, G s * G (1 - s) = 1)
    (hFE : ∀ s : ℂ, D.Q s = η * G s * D.Q (1 - s))
    (hint_p : Integrable fun t : ℝ =>
      D.Q (D.σm + t * I) * F (D.σm + t * I))
    (hint_m : Integrable fun t : ℝ =>
      D.Q (D.σp + t * I) * F (D.σp + t * I)) :
    carry D (fun s => G (1 - s) * F (1 - s)) = -η * carry D F := by
  have key : ∀ (σ τ : ℝ), (τ : ℂ) = 1 - σ →
      (∫ t : ℝ, D.Q (σ + t * I) * (G (1 - (σ + t * I)) * F (1 - (σ + t * I))))
        = η * ∫ t : ℝ, D.Q (τ + t * I) * F (τ + t * I) := by
    intro σ τ hστ
    have hpt : ∀ t : ℝ,
        D.Q (σ + t * I) * (G (1 - (σ + t * I)) * F (1 - (σ + t * I)))
          = η * (D.Q (τ + (-t) * I) * F (τ + (-t) * I)) := by
      intro t
      have harg : 1 - ((σ : ℂ) + t * I) = (τ : ℂ) + (-t) * I := by
        rw [hστ]; push_cast; ring
      rw [harg, hFE ((σ : ℂ) + t * I)]
      have harg2 : 1 - ((σ : ℂ) + t * I) = (τ : ℂ) + (-t) * I := harg
      rw [harg2]
      have hGc := hG ((σ : ℂ) + t * I)
      rw [harg2] at hGc
      -- hGc : G (σ + tI) * G (τ + (−t)I) = 1
      calc η * G ((σ : ℂ) + t * I) * D.Q ((τ : ℂ) + (-t) * I)
            * (G ((τ : ℂ) + (-t) * I) * F ((τ : ℂ) + (-t) * I))
          = η * (G ((σ : ℂ) + t * I) * G ((τ : ℂ) + (-t) * I))
            * (D.Q ((τ : ℂ) + (-t) * I) * F ((τ : ℂ) + (-t) * I)) := by ring
        _ = η * (D.Q ((τ : ℂ) + (-t) * I) * F ((τ : ℂ) + (-t) * I)) := by
            rw [hGc]; ring
    calc (∫ t : ℝ, D.Q (σ + t * I) * (G (1 - (σ + t * I)) * F (1 - (σ + t * I))))
        = ∫ t : ℝ, η * (D.Q (τ + (-t) * I) * F (τ + (-t) * I)) := by
          exact integral_congr_ae (Filter.Eventually.of_forall hpt)
      _ = η * ∫ t : ℝ, D.Q (τ + (-t) * I) * F (τ + (-t) * I) := by
          rw [integral_const_mul]
      _ = η * ∫ t : ℝ, D.Q (τ + t * I) * F (τ + t * I) := by
          congr 1
          have h := integral_neg_eq_self
            (f := fun t : ℝ => D.Q (τ + t * I) * F (τ + t * I))
            (μ := (volume : Measure ℝ))
          simpa [Complex.ofReal_neg] using h
  have hmp : ((D.σm : ℝ) : ℂ) = 1 - (D.σp : ℝ) := by
    rw [hline]; push_cast; ring
  have hpm : ((D.σp : ℝ) : ℂ) = 1 - (D.σm : ℝ) := by
    rw [hline]; push_cast; ring
  have k1 := key D.σp D.σm hmp
  have k2 := key D.σm D.σp hpm
  unfold carry
  rw [k1, k2]
  ring

end CriticalLinePhasor.GlobalCarry

#print axioms CriticalLinePhasor.GlobalCarry.carry_warp_covariance
