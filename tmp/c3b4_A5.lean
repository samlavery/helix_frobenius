import c3b4_A2

/-!
# C3 batch 4 — attack A5.  THE COMPACT REDUCTION

`c3b4_A2`/`c3b4_A4` left the target on the hypothesis

  `hU : ∀ s ≥ 0, 0 ≤ ∫_{(s,∞)} T`,   equivalently   `∫_{(s,∞)} (u−s)²/2·W(u) du ≥ 0`,

a condition quantified over the whole half line.  This file cuts it down to a COMPACT
window, using only the eventual sign of the weight itself.

The analytic input it is designed to consume (attack `att543`): for `u` past
`u₀(x) = ½·log(x/2π)` the cell density is the `n = 1` theta diagonal to high accuracy,

  `C(u,x) ≈ 2[(16π⁴e^{9u} + 36π²e^{5u})K_{ix}(a) + 48π³e^{7u}K′_{ix}(a)]`,  `a = 2πe^{2u}`,

which collapses as `a → ∞` to `8π²e^{5u}(2πe^{2u} − 3)²·K_{ix}(a)` — a PERFECT SQUARE
times a Macdonald function of imaginary order.  `K_{ix}(a) > 0` for `a > x`, so
`C(·,x) ≥ 0` past `u₀`.  Measured agreement with the independent `Ξ` route at
`x = 21.022`: rel. `1.9e-3` at `u = 0.5`, `3.6e-6` at `0.6`, `7.4e-19` at `1.0`.

The theorems below are the abstract consumers, and they assume only
`0 ≤ W` on `(u₀,∞)` — nothing about `K`, `Ξ`, or zeros.

NOTE ON HYPOTHESES.  `tailT_nonneg_of_weight_nonneg` needs NO integrability: if the
integrand fails to be integrable the Bochner integral is `0` by convention, which is
still `≥ 0`.  That is why the reduction is clean.
-/

open MeasureTheory Set

noncomputable section

namespace CriticalLinePhasor.C3B4B

/-- If the weight is nonnegative above `r`, so is its tail primitive at `r`. -/
theorem tailT_nonneg_of_weight_nonneg {W : ℝ → ℝ} {r : ℝ}
    (hW : ∀ u ∈ Ioi r, 0 ≤ W u) : 0 ≤ tailT W r := by
  refine MeasureTheory.setIntegral_nonneg measurableSet_Ioi fun u hu => ?_
  have hu' : r < u := hu
  exact mul_nonneg (by linarith) (hW u hu)

/-- Above the eventual-positivity threshold the tail primitive is nonnegative. -/
theorem tailT_nonneg_above {W : ℝ → ℝ} {u0 : ℝ}
    (hW : ∀ u ∈ Ioi u0, 0 ≤ W u) {r : ℝ} (hr : u0 ≤ r) : 0 ≤ tailT W r :=
  tailT_nonneg_of_weight_nonneg fun u hu => hW u (lt_of_le_of_lt hr hu)

/-- **The second tail primitive is automatically nonnegative above the threshold.**
No compactness, no integrability, no sign information about `W` below `u₀`. -/
theorem second_tail_nonneg_above {W : ℝ → ℝ} {u0 : ℝ}
    (hW : ∀ u ∈ Ioi u0, 0 ≤ W u) {s : ℝ} (hs : u0 ≤ s) :
    0 ≤ ∫ r in Ioi s, tailT W r :=
  MeasureTheory.setIntegral_nonneg measurableSet_Ioi fun r hr =>
    tailT_nonneg_above hW (le_of_lt (lt_of_le_of_lt hs hr))

/-- **THE COMPACT REDUCTION.**  If the weight is eventually nonnegative — from `u₀` on —
then the half-line hypothesis `∀ s ≥ 0, U(s) ≥ 0` follows from its restriction to the
COMPACT window `[0, u₀]`.

This is what the Macdonald-function sign law buys: `u₀(x) = ½ log(x/2π)` is `1.128` at
`x = 60` and `1.320` at `x = 88`, so the open condition is a statement about a window of
length `≈ 1.3`, not about all of `[0,∞)`. -/
theorem second_tail_nonneg_of_compact {W : ℝ → ℝ} {u0 : ℝ}
    (hW : ∀ u ∈ Ioi u0, 0 ≤ W u)
    (hcompact : ∀ s ∈ Icc (0 : ℝ) u0, 0 ≤ ∫ r in Ioi s, tailT W r) :
    ∀ s : ℝ, 0 ≤ s → 0 ≤ ∫ r in Ioi s, tailT W r := by
  intro s hs
  rcases le_total s u0 with h | h
  · exact hcompact s ⟨hs, h⟩
  · exact second_tail_nonneg_above hW h

/-- **THE TARGET, ON A COMPACT WINDOW.**  Composition of the compact reduction with the
layer-cake theorem of `c3b4_A2`.  The only open input is `hcompact`: nonnegativity of the
second tail primitive on `[0, u₀]`. -/
theorem sinh_pairing_nonneg_of_compact {W : ℝ → ℝ} {y u0 : ℝ} (hy : 0 ≤ y)
    (hW : Measurable W)
    (hint : IntegrableOn (fun u => gY y u * |W u|) (Ioi (0 : ℝ)))
    (hprodG : Integrable (Function.uncurry (triG (tailT W) (gY'' y)))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))))
    (hTint : IntegrableOn (tailT W) (Ioi (0 : ℝ)))
    (hqTint : IntegrableOn (fun r => gY'' y r * tailT W r) (Ioi (0 : ℝ)))
    (hWpos : ∀ u ∈ Ioi u0, 0 ≤ W u)
    (hcompact : ∀ s ∈ Icc (0 : ℝ) u0, 0 ≤ ∫ r in Ioi s, tailT W r) :
    0 ≤ ∫ u in Ioi (0 : ℝ), gY y u * W u :=
  sinh_pairing_nonneg_of_second_tail hy hW hint hprodG hTint hqTint
    (second_tail_nonneg_of_compact hWpos hcompact)

/-! ## The perfect square that the Bessel collapse produces

`Φ₁(t) = 2π e^{5t/2}(2π e^{2t} − 3) e^{−π e^{2t}}`, and the large-argument collapse of the
`n = 1` diagonal is `8π²e^{5u}(2πe^{2u} − 3)²·K_{ix}(2πe^{2u})`.  The bracket really is a
square, so the whole sign question at large `u` is carried by `K`. -/
theorem theta_diagonal_perfect_square (u : ℝ) :
    16 * Real.pi ^ 4 * Real.exp (9 * u) - 48 * Real.pi ^ 3 * Real.exp (7 * u)
        + 36 * Real.pi ^ 2 * Real.exp (5 * u)
      = 4 * Real.pi ^ 2 * Real.exp (5 * u)
          * (2 * Real.pi * Real.exp (2 * u) - 3) ^ 2 := by
  have h9 : Real.exp (9 * u) = Real.exp (5 * u) * Real.exp (2 * u) * Real.exp (2 * u) := by
    rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  have h7 : Real.exp (7 * u) = Real.exp (5 * u) * Real.exp (2 * u) := by
    rw [← Real.exp_add]; ring_nf
  rw [h9, h7]
  ring

/-- The bracket is nonnegative for every real `u` — so the `n = 1` diagonal cannot change
sign through its polynomial factor, only through `K_{ix}`. -/
theorem theta_diagonal_bracket_nonneg (u : ℝ) :
    0 ≤ 16 * Real.pi ^ 4 * Real.exp (9 * u) - 48 * Real.pi ^ 3 * Real.exp (7 * u)
        + 36 * Real.pi ^ 2 * Real.exp (5 * u) := by
  rw [theta_diagonal_perfect_square]
  positivity

end CriticalLinePhasor.C3B4B

section AxiomAudit
#print axioms CriticalLinePhasor.C3B4B.tailT_nonneg_of_weight_nonneg
#print axioms CriticalLinePhasor.C3B4B.tailT_nonneg_above
#print axioms CriticalLinePhasor.C3B4B.second_tail_nonneg_above
#print axioms CriticalLinePhasor.C3B4B.second_tail_nonneg_of_compact
#print axioms CriticalLinePhasor.C3B4B.sinh_pairing_nonneg_of_compact
#print axioms CriticalLinePhasor.C3B4B.theta_diagonal_perfect_square
#print axioms CriticalLinePhasor.C3B4B.theta_diagonal_bracket_nonneg
end AxiomAudit
