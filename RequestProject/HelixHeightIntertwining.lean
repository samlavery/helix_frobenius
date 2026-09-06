import RequestProject.HelixHeightCorrespondence

/-!
# The intertwining obligation is the seating (ledger 597)

The correspondence obligation left open by `HelixHeightCorrespondence.lean` is

  `Function.Semiconj zeroHeightCorrespondence xiZeroLedgerOperator (carrierThreeDOperator 1 1)`.

Evaluated on one basis mode `single ρ c` it reads
`single (state Im ρ) (poleParam ρ · c) = single (state Im ρ) (Im ρ · c)`, and
`poleParam ρ − Im ρ = −i (Re ρ − ½)`. So the obligation holds on the mode `ρ` iff `Re ρ = ½`
(`semiconj_single_iff`), holds on every mode iff every zero lies on the line
(`semiconj_iff_online`), and is therefore the seating E3 in the intertwining register — the same
node as `nonempty_coupling_iff`, tagged EQUIV. The forward direction is the compiled
`scaleBalanced_of_height_intertwining`; the converse uses the compiled height intertwining once
`poleParam` is real.
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

/-- If every zero is on the line, the ledger operator is the height operator. -/
theorem xiZeroLedgerOperator_eq_height_of_online (h : ∀ ρ : XiZeroIndex, ρ.val.re = 1 / 2) :
    xiZeroLedgerOperator = xiCarrierHeightOperator := by
  apply Finsupp.lhom_ext
  intro ρ c
  rw [xiZeroLedgerOperator_single', xiCarrierHeightOperator,
    UnconditionalFrobenius.diagOp_single, poleParam_eq_im_of_re_half (h ρ)]

/-- The converse: on-line zeros give the full intertwining. -/
theorem semiconj_of_online (h : ∀ ρ : XiZeroIndex, ρ.val.re = 1 / 2) :
    Function.Semiconj zeroHeightCorrespondence xiZeroLedgerOperator
      (carrierThreeDOperator 1 1) := by
  intro x
  rw [xiZeroLedgerOperator_eq_height_of_online h]
  have := congrArg (fun f => f x) zeroHeightCorrespondence_height_intertwining
  simpa only [LinearMap.comp_apply] using this

/-- The forward direction, from the compiled second-moment residual. -/
theorem online_of_semiconj
    (h : Function.Semiconj zeroHeightCorrespondence xiZeroLedgerOperator
      (carrierThreeDOperator 1 1)) (ρ : XiZeroIndex) : ρ.val.re = 1 / 2 :=
  (carrierScaleBalanced_iff _).1 (scaleBalanced_of_height_intertwining h ρ)

/-- **The intertwining obligation is the seating.** -/
theorem semiconj_iff_online :
    Function.Semiconj zeroHeightCorrespondence xiZeroLedgerOperator (carrierThreeDOperator 1 1)
      ↔ ∀ ρ : XiZeroIndex, ρ.val.re = 1 / 2 :=
  ⟨online_of_semiconj, semiconj_of_online⟩

/-- The same, quantified over the zero set. -/
theorem semiconj_iff_nontrivialZeros_online :
    Function.Semiconj zeroHeightCorrespondence xiZeroLedgerOperator (carrierThreeDOperator 1 1)
      ↔ ∀ ρ ∈ ZD.NontrivialZeros, ρ.re = 1 / 2 := by
  rw [semiconj_iff_online]
  exact ⟨fun h ρ hρ => h ⟨ρ, hρ⟩, fun h ρ => h ρ.val ρ.2⟩

end CriticalLinePhasor.XiChannel

#print axioms CriticalLinePhasor.XiChannel.semiconj_single_iff
#print axioms CriticalLinePhasor.XiChannel.semiconj_iff_online
#print axioms CriticalLinePhasor.XiChannel.semiconj_iff_nontrivialZeros_online
