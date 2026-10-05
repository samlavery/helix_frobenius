import RequestProject.HelixHeightCorrespondence

/-!
# The intertwining obligation is the seating (ledger 597)

The correspondence obligation left open by `HelixHeightCorrespondence.lean` is

  `Function.Semiconj zeroHeightCorrespondence xiZeroLedgerOperator (carrierThreeDOperator 1 1)`.

Evaluated on one basis mode `single ρ c` it reads
`single (state Im ρ) (poleParam ρ · c) = single (state Im ρ) (Im ρ · c)`, and
`poleParam ρ − Im ρ = −i (Re ρ − ½)`. So the obligation holds on the mode `ρ` iff `Re ρ = ½`
(`semiconj_single_iff`), and if it holds on every mode every zero lies on the line
(`online_of_semiconj`): it is the seating E3 in the intertwining register. The door is the compiled
`scaleBalanced_of_height_intertwining`.
-/

open Complex

namespace CriticalLinePhasor.XiChannel

open ThreeDFocal

/-- On the line the pole parameter is the height. -/
theorem poleParam_eq_im_of_re_half {ρ : ℂ} (h : ρ.re = 1 / 2) :
    HelixLimit.poleParam ρ = (ρ.im : ℂ) := by
  simp [HelixLimit.poleParam, h]

/-- On one basis mode the obligation is exactly `Re ρ = ½`. -/
theorem semiconj_single_iff (ρ : XiZeroIndex) :
    zeroHeightCorrespondence (xiZeroLedgerOperator (Finsupp.single ρ 1))
        = carrierThreeDOperator 1 1 (zeroHeightCorrespondence (Finsupp.single ρ 1))
      ↔ ρ.val.re = 1 / 2 := by
  rw [xiZeroLedgerOperator_single', zeroHeightCorrespondence_single,
    zeroHeightCorrespondence_single, carrierThreeDOperator_single', mul_one, mul_one]
  constructor
  · intro h
    have h1 := Finsupp.single_injective (carrierState3D 1 1 ρ.val.im) h
    have h2 := congrArg Complex.im h1
    simp [HelixLimit.poleParam] at h2
    linarith
  · intro h
    rw [poleParam_eq_im_of_re_half h]
    rfl

/-- The door, from the compiled second-moment residual. -/
theorem online_of_semiconj
    (h : Function.Semiconj zeroHeightCorrespondence xiZeroLedgerOperator
      (carrierThreeDOperator 1 1)) (ρ : XiZeroIndex) : ρ.val.re = 1 / 2 :=
  (carrierScaleBalanced_iff _).1 (scaleBalanced_of_height_intertwining h ρ)

/-- The same door, quantified over the zero set. -/
theorem online_of_semiconj_nontrivialZeros
    (h : Function.Semiconj zeroHeightCorrespondence xiZeroLedgerOperator
      (carrierThreeDOperator 1 1)) :
    ∀ ρ ∈ ZD.NontrivialZeros, ρ.re = 1 / 2 :=
  fun ρ hρ => online_of_semiconj h ⟨ρ, hρ⟩

end CriticalLinePhasor.XiChannel

#print axioms CriticalLinePhasor.XiChannel.semiconj_single_iff
#print axioms CriticalLinePhasor.XiChannel.online_of_semiconj_nontrivialZeros
