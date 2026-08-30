import RequestProject.RiemannHypothesisBridge
import RequestProject.SeatingMassWrap
import RequestProject.SeatingHighFlips
import RequestProject.SeatingLensCayley

/-!
# Endpoint forms: the doors composed to Mathlib's `RiemannHypothesis`

The exact-target census.  Each principal door, composed through the
compiled bridge (`RHBridge.no_offline_zeros_implies_rh`) to the exact
Mathlib proposition `RiemannHypothesis` — so every route's conclusion is
the final proposition itself, not a project-local normal form.

No `sorry`, no `axiom`.
-/

noncomputable section

namespace CriticalLinePhasor.SeatingLedger

/-- **Mathlib RH from channel mass nonnegativity.** -/
theorem riemannHypothesis_of_channel_mass :
    ∃ A : ℝ, 0 < A ∧
      ((∀ s : ℂ, 1269/2 < |s.im| →
          A / (Real.log |s.im|)^9 < s.re → s.re < 1/2 →
          0 ≤ seatMass s) →
        RiemannHypothesis) := by
  obtain ⟨A, hA0, h⟩ := rh_of_channel_mass
  exact ⟨A, hA0, fun hM => RHBridge.no_offline_zeros_implies_rh (h hM)⟩

/-- **Mathlib RH from high flip visibility.** -/
theorem riemannHypothesis_of_high_flip_visibility
    (h : ∀ T₁ T₂ : ℝ, 1269/2 ≤ T₁ → T₁ < T₂ → ∃ (n : ℕ) (a : Fin (n+1) → ℝ),
      (stripBox T₁ T₂).ncard ≤ n ∧ StrictMono a ∧ T₁ ≤ a 0 ∧
      a (Fin.last n) ≤ T₂ ∧
      ∀ i : Fin n, XiLine (a i.castSucc) * XiLine (a i.succ) < 0) :
    RiemannHypothesis :=
  RHBridge.no_offline_zeros_implies_rh (rh_of_high_flip_visibility h)

/-- **Mathlib RH from a Cayley lens-matching unitary.** -/
theorem riemannHypothesis_of_lens_cayley_two_point
    {A : Type*} [CStarAlgebra A] {u : A} (hu : u ∈ unitary A)
    {φ : A → ℂ} (hφ : Continuous φ)
    {z₀ : ℂ} (hz₀ : (1/2 + Complex.I * z₀) ∉ ZD.NontrivialZeros) :
    ∃ c : ℝ, 0 < c ∧
      ((∀ z : ℂ, z.im ≠ 0 → 1269/2 < |z.re| →
          |z.im| < 1/2 - c / (Real.log |z.re|)^9 →
          φ (resolvent u ((z - Complex.I)/(z + Complex.I)))
            - φ (resolvent u ((z₀ - Complex.I)/(z₀ + Complex.I)))
            = ∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
                (ZD.xiOrderNat ρ.val : ℂ) *
                  ((CriticalLinePhasor.HilbertPolya.spectralCoord ρ.val - z)⁻¹
                    - (CriticalLinePhasor.HilbertPolya.spectralCoord ρ.val - z₀)⁻¹)) →
        RiemannHypothesis) := by
  obtain ⟨c, hc0, h⟩ := rh_of_lens_cayley_two_point hu hφ hz₀
  exact ⟨c, hc0, fun hid => RHBridge.no_offline_zeros_implies_rh (h hid)⟩

end CriticalLinePhasor.SeatingLedger

#print axioms CriticalLinePhasor.SeatingLedger.riemannHypothesis_of_channel_mass
#print axioms CriticalLinePhasor.SeatingLedger.riemannHypothesis_of_high_flip_visibility
#print axioms CriticalLinePhasor.SeatingLedger.riemannHypothesis_of_lens_cayley_two_point
