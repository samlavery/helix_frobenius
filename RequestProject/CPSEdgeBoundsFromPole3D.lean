import RequestProject.CPSEdgePoleTolerantEngine3D

/-!
# The edge growth bounds are free

`bank_edge_nonvanishing_of_simplePole` asks for two quantitative hypotheses on the pair-bank
readout `D`: that `(σ-1)‖D(σ)‖` is bounded on `(1,2]`, and that `‖D(σ+2yi)‖` is bounded there.
Carrying those as fields of a rank-uniform interface is the wrong shape — they are not extra
arithmetic input, they are consequences of the pole structure.

Both follow from one qualitative statement: **`D` has at most a simple pole at `s = 1`**, i.e.
`D = E/(s-1)` on the half-plane with `E` continuous.  Then

* on the real segment, `(σ-1)‖D(σ)‖ = ‖E(σ)‖`, bounded by compactness — the pole is cancelled
  exactly, not estimated;
* on the twisted segment, `‖s-1‖ ≥ |2y| > 0` because the imaginary part alone is `2y`, so the
  pole is never approached at all and `‖D‖ ≤ ‖E‖/(2|y|)`.

The second is the harmonic point: off the real axis the simple pole is not a difficulty of size
`1/(σ-1)` that has to be dominated — the twist itself bounds the denominator away from zero, and
the distance is set by the twist frequency `y`, the object's own scale.

Consequence: `bank_edge_nonvanishing_of_holomorphic_pair` needs no growth hypotheses at all.  Two
fields come off the interface; what remains is the pole structure, which is where the arithmetic
actually lives.

**Scope.**  This is an interface result about the edge engine.  It supplies no new arithmetic.
-/

open Complex Filter
open scoped Real Topology

namespace CriticalLinePhasor.ThreeDConverse

/-- **The edge bounds follow from a simple pole.**  No estimate is made: on the real segment the
pole cancels exactly, and on the twisted segment it is never approached. -/
theorem edge_bounds_of_simplePole {D E : ℂ → ℂ} (hE : Continuous E)
    (hDE : ∀ s : ℂ, 1 < s.re → D s = E s / (s - 1)) {y : ℝ} (hy : y ≠ 0) :
    ∃ K K₂ : ℝ,
      (∀ σ : ℝ, 1 < σ → σ ≤ 2 → ‖D (σ : ℂ)‖ * (σ - 1) ≤ K) ∧
      (∀ σ : ℝ, 1 < σ → σ ≤ 2 → ‖D ((σ : ℂ) + 2 * y * I)‖ ≤ K₂) := by
  have hyabs : (0:ℝ) < 2 * |y| := by
    have : (0:ℝ) < |y| := abs_pos.mpr hy
    linarith
  -- bounds on the two compact segments
  obtain ⟨B₁, hB₁⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (f := fun σ : ℝ => E (σ : ℂ))
    (hE.comp Complex.continuous_ofReal).continuousOn
  obtain ⟨B₂, hB₂⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Set.Icc (1:ℝ) 2) (f := fun σ : ℝ => E ((σ : ℂ) + 2 * y * I))
    (by fun_prop)
  refine ⟨B₁, B₂ / (2 * |y|), fun σ hσ hσ2 => ?_, fun σ hσ hσ2 => ?_⟩
  · -- real segment: the pole cancels exactly
    have hre : ((σ : ℂ)).re = σ := Complex.ofReal_re σ
    rw [hDE _ (by rw [hre]; exact hσ), norm_div]
    have hsub : ‖(σ : ℂ) - 1‖ = σ - 1 := by
      rw [show (σ : ℂ) - 1 = ((σ - 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (by linarith)]
    rw [hsub, div_mul_cancel₀ _ (by linarith : σ - 1 ≠ 0)]
    exact hB₁ σ ⟨hσ.le, hσ2⟩
  · -- twisted segment: the twist bounds the denominator away from zero
    have hre : ((σ : ℂ) + 2 * y * I).re = σ := by simp
    have hden : 2 * |y| ≤ ‖(σ : ℂ) + 2 * y * I - 1‖ := by
      have him : ((σ : ℂ) + 2 * y * I - 1).im = 2 * y := by simp
      have h := Complex.abs_im_le_norm ((σ : ℂ) + 2 * y * I - 1)
      rw [him] at h
      calc 2 * |y| = |2 * y| := by rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
        _ ≤ _ := h
    rw [hDE _ (by rw [hre]; exact hσ), norm_div, div_le_div_iff₀ (by linarith) hyabs]
    have hnum : ‖E ((σ : ℂ) + 2 * y * I)‖ ≤ B₂ := hB₂ σ ⟨hσ.le, hσ2⟩
    have hB₂0 : (0:ℝ) ≤ B₂ := le_trans (norm_nonneg _) hnum
    exact mul_le_mul hnum hden (le_of_lt hyabs) hB₂0

/-- **Edge non-vanishing with no growth hypotheses.**  The pair-bank readout having at most a
simple pole at `s = 1` is the whole analytic input; the two quantitative fields of
`bank_edge_nonvanishing_of_simplePole` come off the interface. -/
theorem bank_edge_nonvanishing_of_holomorphic_pair {m : ℕ} (α : Nat.Primes → Fin m → ℂ)
    (hα : ∀ p i, ‖α p i‖ = 1)
    (hreal : ∀ (p : Nat.Primes) (n : ℕ), (∑ i, α p i ^ n).im = 0)
    {C D E : ℂ → ℂ} (hC : Differentiable ℂ C)
    (hCeq : Set.EqOn C (bankEulerReadout α) {s : ℂ | 1 < s.re})
    (hDeq : Set.EqOn D (bankEulerReadout (pairBank α)) {s : ℂ | 1 < s.re})
    (hE : Continuous E) (hDE : ∀ s : ℂ, 1 < s.re → D s = E s / (s - 1))
    {y : ℝ} (hy : y ≠ 0) :
    C (1 + y * I) ≠ 0 := by
  obtain ⟨K, K₂, hK, hK₂⟩ := edge_bounds_of_simplePole hE hDE hy
  exact bank_edge_nonvanishing_of_simplePole α hα hreal hC hCeq hDeq hK hK₂

/-- **Non-vanishing on the closed half-plane reduces to the single point `s = 1`.**

Off the line it is free: the bank readout is `exp` of the Euler log, and an exponential never
vanishes — no arithmetic is used at all.  On the line minus the real point it is the edge argument,
which by `edge_bounds_of_simplePole` needs only the pair bank's pole structure.  What is left is
`C 1 ≠ 0`, one point.

So the non-vanishing half of a rank-uniform analytic interface is not a half-plane hypothesis; it
is a one-point hypothesis plus the pole structure. -/
theorem bank_cand_ne_of_pole_and_one {m : ℕ} (α : Nat.Primes → Fin m → ℂ)
    (hα : ∀ p i, ‖α p i‖ = 1)
    (hreal : ∀ (p : Nat.Primes) (n : ℕ), (∑ i, α p i ^ n).im = 0)
    {C D E : ℂ → ℂ} (hC : Differentiable ℂ C)
    (hCeq : Set.EqOn C (bankEulerReadout α) {s : ℂ | 1 < s.re})
    (hDeq : Set.EqOn D (bankEulerReadout (pairBank α)) {s : ℂ | 1 < s.re})
    (hE : Continuous E) (hDE : ∀ s : ℂ, 1 < s.re → D s = E s / (s - 1))
    (hone : C 1 ≠ 0) :
    ∀ s : ℂ, 1 ≤ s.re → C s ≠ 0 := by
  intro s hs
  rcases lt_or_eq_of_le hs with hgt | heq
  · -- off the line: the Euler product is an exponential
    rw [hCeq (Set.mem_ofPred.mpr hgt), bankEulerReadout]
    exact Complex.exp_ne_zero _
  · have hre : s.re = 1 := heq.symm
    rcases eq_or_ne s.im 0 with him | him
    · have hs1 : s = 1 := by
        apply Complex.ext <;> simp [hre, him]
      rw [hs1]
      exact hone
    · have hs1 : s = 1 + s.im * I := by
        apply Complex.ext <;> simp [hre]
      rw [hs1]
      exact bank_edge_nonvanishing_of_holomorphic_pair α hα hreal hC hCeq hDeq hE hDE him

end CriticalLinePhasor.ThreeDConverse

#print axioms CriticalLinePhasor.ThreeDConverse.edge_bounds_of_simplePole
#print axioms CriticalLinePhasor.ThreeDConverse.bank_edge_nonvanishing_of_holomorphic_pair
#print axioms CriticalLinePhasor.ThreeDConverse.bank_cand_ne_of_pole_and_one
