import c3b16_A1

/-!
# C3 batch 16, block A2 — strict positivity of the mass, and what it buys

`no_adaptive_window_of_witness` needs a witness `c > 0` with `mass/4 < Tail c`.  The natural
route to producing one is: `Tail 0 = mass/2` (compiled, `C3B16.Tail_zero`), `Tail` is
continuous at `0`, and `mass/2 > mass/4` — the last step requiring **`0 < mass`**, which is
what this block supplies.

`mass = cosMom Rker 0 = ¼·(∫Φ)·(∫t²Φ)` by `C3B14.cosMom_Rker` at `x = 0`, and both factors
are strictly positive because `Φ > 0` everywhere (`riemannXiKernel_pos_all`), so their
supports are all of `ℝ`.

**What is still missing for an unconditional exclusion, named precisely.**  With `mass > 0`
and `Tail 0 = mass/2`, a witness exists as soon as `Tail` is continuous from the right at `0`
— equivalently, as soon as `c ↦ ∫_{(0,c]}R` tends to `0`, which is absolute continuity of the
integral of the integrable `R`.  **That continuity step is NOT formalised here.**  Until it
is, the exclusion remains conditional on the numeric witness (`c = 0.05`, measured
`Tail c = 4.168e−03` against `mass/4 = 2.855e−03`).  This is stated rather than glossed.

SCOPE: strict positivity of three integrals, and the exact statement of the remaining gap.
-/

open MeasureTheory Set Filter Topology

noncomputable section

namespace C3B16

open CriticalLinePhasor.ThetaWronskianSuzukiGram
open C3B10
open C3B11
open C3B12
open C3B13
open C3B14
open C3B15

/-! ### 1. The two arithmetic-free positivity facts -/

theorem cosMom_xiKernel_zero_pos : 0 < cosMom riemannXiKernel 0 := by
  rw [cosMom_at_zero]
  rw [integral_pos_iff_support_of_nonneg xiKernel_nonneg xiKernel_integrable]
  have hsupp : Function.support riemannXiKernel = univ := by
    ext t
    simp only [Function.mem_support, mem_univ, iff_true]
    exact ne_of_gt (C3B5.A1.riemannXiKernel_pos_all t)
  rw [hsupp]
  simp

theorem cosMom_kM2_zero_pos : 0 < cosMom kM2 0 := by
  rw [cosMom_at_zero]
  rw [integral_pos_iff_support_of_nonneg kM2_nonneg kM2_integrable]
  have hsub : Ioi (1 : ℝ) ⊆ Function.support kM2 := by
    intro t ht
    have h1 : (0:ℝ) < t := lt_trans zero_lt_one ht
    have hpos : 0 < riemannXiKernel t := C3B5.A1.riemannXiKernel_pos_all t
    simp only [Function.mem_support]
    unfold kM2
    positivity
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  rw [Real.volume_Ioi]
  simp

/-! ### 2. THE MASS IS STRICTLY POSITIVE -/

/-- **`0 < mass`.**  Through `C3B14.cosMom_Rker` at `x = 0`, the mass is
`¼·(∫Φ)·(∫t²Φ)`, and both factors are positive because `Φ > 0` everywhere. -/
theorem mass_pos : 0 < cosMom Rker 0 := by
  have h := cosMom_Rker 0
  rw [mul_zero] at h
  rw [h, sinMom_at_zero]
  have h1 := cosMom_xiKernel_zero_pos
  have h2 := cosMom_kM2_zero_pos
  have : 0 < cosMom riemannXiKernel 0 * cosMom kM2 0 := mul_pos h1 h2
  nlinarith [this]

/-! ### 3. What the witness buys, and the exact remaining gap -/

/-- With `mass > 0`, the witness inequality `mass/4 < Tail c` is **strictly weaker** than the
compiled `Tail 0 = mass/2`: the witness asks only that a *positive* radius still retains more
than a quarter of the mass, where radius `0` retains exactly half. -/
theorem witness_holds_at_zero : cosMom Rker 0 / 4 < Tail 0 := by
  rw [Tail_zero]
  linarith [mass_pos]

/-- **THE REMAINING GAP, STATED AS A THEOREM.**  If `Tail` is right-continuous at `0` in the
weak sense that some positive radius keeps more than a quarter of the mass, the exclusion is
unconditional.  This isolates the missing analytic input to a single existential, and proves
everything downstream of it. -/
theorem no_adaptive_window_of_exists_witness
    (hex : ∃ c : ℝ, 0 < c ∧ cosMom Rker 0 / 4 < Tail c) :
    ∃ X : ℝ, ∀ a x : ℝ, 0 ≤ a → 4 * Tail a ≤ cosMom Rker 0 →
      2 * x ^ 2 * Qwin a + 4 * Tail a ≤ cosMom Rker 0 → x ^ 2 ≤ X := by
  obtain ⟨c, hc, hw⟩ := hex
  refine ⟨cosMom Rker 0 / (2 * (2 * c ^ 2 * (Tail c - cosMom Rker 0 / 4))), ?_⟩
  intro a x ha hadm hcrit
  exact no_adaptive_window_of_witness hc hw ha hadm hcrit

end C3B16

section AxiomAudit
#print axioms C3B16.cosMom_xiKernel_zero_pos
#print axioms C3B16.cosMom_kM2_zero_pos
#print axioms C3B16.mass_pos
#print axioms C3B16.witness_holds_at_zero
#print axioms C3B16.no_adaptive_window_of_exists_witness
end AxiomAudit
