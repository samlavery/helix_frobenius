import RequestProject.PencilCellEdgeDoor
import RequestProject.SeatingStageDoor
import RequestProject.WeilDuality
import RequestProject.DVPLadder1269o2

/-!
# Frobenius-weight candidate audit

This file checks the three positive-object registers against the exact hypotheses of
`riemannHypothesis_of_frobenius_weight`.

The target unfolds to a function `P : ℂ → ℝ` such that, at every nontrivial zero `ρ`,

* `0 < P ρ`;
* `P (1 - conj ρ) = P ρ`;
* `‖exp (ρ.re - 1 / 2)‖ ^ 2 * P ρ = P (1 - conj ρ)`.

The seat mass supplies the second line, but at every zero it is exactly zero.  The
control weight supplies the first and third lines.  Their product with a positive
seat-mass factor gives a concrete candidate whose only remaining field is Frobenius
invariance.  The Weil tensor-power register gives a second route: bounds for both end
faces feed `WeilDuality.purity_engine`, after which the constant weight `P = 1`
inhabits the Frobenius-weight door.

Search audit (repo and Mathlib, with naming variants):

```
rg -n -S "riemannHypothesis_of_frobenius_weight|frobenius[_A-Za-z]*weight|Frobenius.{0,30}weight"
rg -n -S \
  "face_norm_one_of_invariant_weight|control_weight_pos_sim|invariant.*weight|weight.*invariant"
rg -n -S "finiteBank_seatMass_nonneg|finiteBank.*logDeriv.*im.*nonpos|seatMass|mass_mirror"
rg -n -S "endExchange|endPairFace|endPair_det_one|similitude|tensor_power_purity|purity_engine"
rg -n -S "NontrivialZeros|RiemannHypothesis|no_offline_zeros_implies_rh"
```

The same searches under `.lake/packages/mathlib/Mathlib/` found only Mathlib's
definition of `RiemannHypothesis`; the project-specific candidate declarations occur in
the files imported above.
-/

open Complex

noncomputable section

namespace CriticalLinePhasor.FrobeniusWeightCandidateAudit

open CriticalLinePhasor.CellEdgeDoor
open CriticalLinePhasor.SeatingLedger

/-! ## The seating-mass register -/

/-- The compiled seat mass is Frobenius-invariant at every point. -/
theorem seatMass_endExchange (ρ : ℂ) :
    seatMass (endExchange ρ) = seatMass ρ := by
  simpa [endExchange] using seatMass_mirror ρ

/-- At every nontrivial zero, the seat mass is exactly zero. -/
theorem seatMass_eq_zero_at_nontrivialZero {ρ : ℂ} (hρ : ρ ∈ ZD.NontrivialZeros) :
    seatMass ρ = 0 :=
  seatMass_eq_zero_of_zero ((ZD.riemannXi_eq_zero_iff ρ).mpr hρ)

/-- Consequently the seat mass cannot supply the strict-positive field of D7 at a zero. -/
theorem seatMass_not_pos_at_nontrivialZero {ρ : ℂ} (hρ : ρ ∈ ZD.NontrivialZeros) :
    ¬ 0 < seatMass ρ := by
  rw [seatMass_eq_zero_at_nontrivialZero hρ]
  norm_num

/-! ## The control weight, combined with the invariant seating factor -/

/-- The explicit control weight from `control_weight_pos_sim`. -/
def controlWeight (ρ : ℂ) : ℝ := Real.exp (-ρ.re)

theorem controlWeight_pos (ρ : ℂ) : 0 < controlWeight ρ :=
  Real.exp_pos _

/-- The control weight is intertwined with the end-face similitude. -/
theorem controlWeight_sim (ρ : ℂ) :
    ‖endPairFace ρ‖ ^ 2 * controlWeight ρ = controlWeight (endExchange ρ) := by
  simp only [controlWeight, norm_endPairFace]
  unfold endExchange
  simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
  rw [pow_two, ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

/-- Invariance of the control weight at one point is exactly the fixed-abscissa equation. -/
theorem controlWeight_invariant_iff_online (ρ : ℂ) :
    controlWeight (endExchange ρ) = controlWeight ρ ↔ ρ.re = 1 / 2 := by
  unfold controlWeight endExchange
  simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
  rw [Real.exp_eq_exp]
  constructor <;> intro h <;> linarith

/-- A seat-decorated control weight.  The square makes the seating factor nonnegative
everywhere, and it equals one at each nontrivial zero. -/
def seatedControlWeight (ρ : ℂ) : ℝ :=
  controlWeight ρ * (1 + seatMass ρ) ^ 2

theorem seatedControlWeight_pos_at_nontrivialZero {ρ : ℂ}
    (hρ : ρ ∈ ZD.NontrivialZeros) : 0 < seatedControlWeight ρ := by
  rw [seatedControlWeight, seatMass_eq_zero_at_nontrivialZero hρ]
  simpa using controlWeight_pos ρ

/-- The seated control weight inherits the control weight's similitude law because the
seat factor is Frobenius-invariant. -/
theorem seatedControlWeight_sim (ρ : ℂ) :
    ‖endPairFace ρ‖ ^ 2 * seatedControlWeight ρ =
      seatedControlWeight (endExchange ρ) := by
  unfold seatedControlWeight
  rw [seatMass_endExchange]
  calc
    ‖endPairFace ρ‖ ^ 2 * (controlWeight ρ * (1 + seatMass ρ) ^ 2) =
        (‖endPairFace ρ‖ ^ 2 * controlWeight ρ) * (1 + seatMass ρ) ^ 2 := by ring
    _ = controlWeight (endExchange ρ) * (1 + seatMass ρ) ^ 2 := by
      rw [controlWeight_sim]

/-- On the zero set, invariance of the seated candidate reduces to the fixed-abscissa
equation; the invariant seat-mass factor contributes exactly one there. -/
theorem seatedControlWeight_invariant_iff_online {ρ : ℂ}
    (hρ : ρ ∈ ZD.NontrivialZeros) :
    seatedControlWeight (endExchange ρ) = seatedControlWeight ρ ↔ ρ.re = 1 / 2 := by
  have hFρ : endExchange ρ ∈ ZD.NontrivialZeros := endExchange_mem hρ
  rw [seatedControlWeight, seatedControlWeight,
    seatMass_eq_zero_at_nontrivialZero hρ,
    seatMass_eq_zero_at_nontrivialZero hFρ]
  simpa using controlWeight_invariant_iff_online ρ

/-- The exact remaining field for the explicit seated candidate. -/
theorem riemannHypothesis_of_seatedControlWeight_invariant
    (hinv : ∀ ρ ∈ ZD.NontrivialZeros,
      seatedControlWeight (endExchange ρ) = seatedControlWeight ρ) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_frobenius_weight seatedControlWeight
  · exact fun ρ hρ => seatedControlWeight_pos_at_nontrivialZero hρ
  · exact hinv
  · exact fun ρ _ => seatedControlWeight_sim ρ

/-! ## The Weil tensor-power register -/

/-- Tensor-power cup bounds on both ends of one det-one pair force its first face to
have unit norm. -/
theorem face_norm_one_of_two_sided_power_bounds {ρ : ℂ} {C₁ C₂ : ℝ}
    (hC₁ : 0 < C₁) (hC₂ : 0 < C₂)
    (h₁ : ∀ k : ℕ, ‖endPairFace ρ‖ ^ (2 * k) ≤ C₁)
    (h₂ : ∀ k : ℕ, ‖endPairFace (endExchange ρ)‖ ^ (2 * k) ≤ C₂) :
    ‖endPairFace ρ‖ = 1 := by
  have hpure := CriticalLinePhasor.WeilDuality.purity_engine
    (α := endPairFace ρ) (β := endPairFace (endExchange ρ))
    (B := 1) (Cα := C₁) (Cβ := C₂) (by norm_num) hC₁ hC₂
    (by simpa [endExchange] using endPair_det_one ρ)
    (fun k => by simpa using h₁ k) (fun k => by simpa using h₂ k)
  simpa using hpure.1

/-- On the critical line, both inverse end faces have all even powers bounded
by one. -/
theorem endPairFace_two_sided_power_bounds_of_online {ρ : ℂ}
    (hre : ρ.re = 1 / 2) :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∃ C₂ : ℝ, 0 < C₂ ∧
      (∀ k : ℕ, ‖endPairFace ρ‖ ^ (2 * k) ≤ C₁) ∧
      ∀ k : ℕ, ‖endPairFace (endExchange ρ)‖ ^ (2 * k) ≤ C₂ := by
  have hface : ‖endPairFace ρ‖ = 1 := by
    rw [norm_endPairFace, hre]
    norm_num
  have hexchange : (endExchange ρ).re = 1 / 2 := by
    unfold endExchange
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
    rw [hre]
    norm_num
  have hfaceExchange : ‖endPairFace (endExchange ρ)‖ = 1 := by
    rw [norm_endPairFace, hexchange]
    norm_num
  refine ⟨1, one_pos, 1, one_pos, ?_, ?_⟩
  · intro k
    rw [hface]
    norm_num
  · intro k
    rw [hfaceExchange]
    norm_num

/-- The compiled DVP ladder supplies the two-sided end-face bounds for every
nontrivial zero up to height `1269/2`. -/
theorem endPairFace_two_sided_power_bounds_below_1269o2 {ρ : ℂ}
    (hρ : ρ ∈ ZD.NontrivialZeros) (hheight : |ρ.im| ≤ 1269 / 2) :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∃ C₂ : ℝ, 0 < C₂ ∧
      (∀ k : ℕ, ‖endPairFace ρ‖ ^ (2 * k) ≤ C₁) ∧
      ∀ k : ℕ, ‖endPairFace (endExchange ρ)‖ ^ (2 * k) ≤ C₂ := by
  apply endPairFace_two_sided_power_bounds_of_online
  exact CriticalLinePhasor.DVP.online_below_1269o2 ρ hρ hheight

/-- The Weil-rung door in D7 form: two-sided tensor-power bounds at every zero make
the constant positive invariant weight `P = 1` satisfy the similitude law. -/
theorem riemannHypothesis_of_two_sided_face_power_bounds
    (hbound : ∀ ρ ∈ ZD.NontrivialZeros,
      ∃ C₁ : ℝ, 0 < C₁ ∧ ∃ C₂ : ℝ, 0 < C₂ ∧
        (∀ k : ℕ, ‖endPairFace ρ‖ ^ (2 * k) ≤ C₁) ∧
        ∀ k : ℕ, ‖endPairFace (endExchange ρ)‖ ^ (2 * k) ≤ C₂) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_frobenius_weight (fun _ => 1)
  · intro ρ hρ
    norm_num
  · intro ρ hρ
    rfl
  · intro ρ hρ
    obtain ⟨C₁, hC₁, C₂, hC₂, h₁, h₂⟩ := hbound ρ hρ
    rw [face_norm_one_of_two_sided_power_bounds hC₁ hC₂ h₁ h₂]
    norm_num

end CriticalLinePhasor.FrobeniusWeightCandidateAudit

open CriticalLinePhasor.FrobeniusWeightCandidateAudit

#print axioms seatMass_endExchange
#print axioms seatMass_eq_zero_at_nontrivialZero
#print axioms seatMass_not_pos_at_nontrivialZero
#print axioms controlWeight_sim
#print axioms seatedControlWeight_sim
#print axioms seatedControlWeight_invariant_iff_online
#print axioms riemannHypothesis_of_seatedControlWeight_invariant
#print axioms face_norm_one_of_two_sided_power_bounds
#print axioms endPairFace_two_sided_power_bounds_of_online
#print axioms endPairFace_two_sided_power_bounds_below_1269o2
#print axioms riemannHypothesis_of_two_sided_face_power_bounds
