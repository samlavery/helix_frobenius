import RequestProject.GlobalHelixCPSDualPair

/-!
# Control: the synthesized-kernel readout carries no Satake data

A falsification-register entry, machine-checked.

`GlobalHelixCPSDualPair` builds `cpsPrimalCarrierKernel r α τ` as the **Dirichlet inverse of
the bank's own coefficient arithmetic**, dilated against the completed carrier.  Pairing a
bank with the Dirichlet inverse of that same bank reconstructs the carrier exactly
(`theta_dirichletInverse_coupling`), so the resulting readout is the carrier — the same
function for every rank, every prime phase, and every twist family.

* `cpsPrimal3DBankReadout_eq_carrier` — the readout **is**
  `completedLogTheta twistedSymmetricPowerExchangeCarrier 1`, at every positive height;
* `cpsPrimal3DBankReadout_independent_of_satake` — hence two readouts built from entirely
  different Satake data (different rank, different phase, different twist type) are equal.

**Consequence for how the corpus is read.**  `cpsDualPair_twistedNiceness` and
`cpsAllTwists_twistedNiceness` are true theorems about `cpsDualPairStrongFEPair`, and by the
above that pair's `Λ` is the Mellin transform of the carrier.  They are therefore statements
about the carrier's own regularity, and do not by themselves establish entirety, vertical-strip
boundedness, or a functional equation for any L-function attached to `α` or `τ`.

**This does not touch the prescribed-kernel route.**
`cpsPolynomialFullPrimal3DBankReadout W C μs` pairs the bank against
`conductorScaledCompletionKernelLog C μs`, which is built from `C` and `μs` alone and does
not mention `W`.  That readout does depend on the Satake data, and it is the object the
coupling machinery (`BankThetaProfileCoupling3D`, `rsCoupling_of_lineAgreement`,
`BankThetaProfileCoupling3D.ofAxisReality`) consumes.  The distinction between the two
kernels is exactly the distinction between a reconstruction identity and an arithmetic
theorem.

The design law this enforces: a control must fail by *missing structure*, never by more
cancellation.  Here the control fails by reconstruction — the kernel was solved for.

No `axiom`, no `sorry`.
-/

open Complex

namespace CriticalLinePhasor.GlobalHelix

open CriticalLinePhasor.CarrierTheta CriticalLinePhasor.StrandExchange

/-- **The synthesized-kernel readout is the carrier.**  Pairing the all-place bank with the
Dirichlet inverse of its own coefficient arithmetic reconstructs
`completedLogTheta twistedSymmetricPowerExchangeCarrier 1` exactly, at every rank and every
Satake family. -/
theorem cpsPrimal3DBankReadout_eq_carrier
    {κ : Type*} [Fintype κ] (r : ℕ) (α : UnitaryPrimePhase)
    (τ : UnitarySatakeFamily κ) {x : ℝ} (hx : 0 < x) :
    cpsPrimal3DBankReadout r α τ x =
      completedLogTheta twistedSymmetricPowerExchangeCarrier 1 x := by
  rw [cpsPrimal3DBankReadout_eq_theta r α τ hx]
  exact theta_dirichletInverse_completedLogTheta_of_polynomial
    (cpsPrimalSatakeCoeff r α τ) (cpsPrimalCoefficientOneInvertible r α τ)
    twistedSymmetricPowerExchangeCarrier 1 0
    twistedSymmetricPowerExchangeCarrier_logTheta_isBigO
    (Fintype.card (Fin (r + 1) × κ)) 1 zero_le_one
    (cpsPrimalCoefficientArithmetic_norm_le r α τ) hx

/-- **The readout does not depend on the Satake data.**  Different rank, different prime
phase, different twist family — even a different twist *type* — give the same function. -/
theorem cpsPrimal3DBankReadout_independent_of_satake
    {κ κ' : Type*} [Fintype κ] [Fintype κ']
    (r r' : ℕ) (α α' : UnitaryPrimePhase)
    (τ : UnitarySatakeFamily κ) (τ' : UnitarySatakeFamily κ')
    {x : ℝ} (hx : 0 < x) :
    cpsPrimal3DBankReadout r α τ x = cpsPrimal3DBankReadout r' α' τ' x := by
  rw [cpsPrimal3DBankReadout_eq_carrier r α τ hx,
    cpsPrimal3DBankReadout_eq_carrier r' α' τ' hx]

end CriticalLinePhasor.GlobalHelix

#print axioms CriticalLinePhasor.GlobalHelix.cpsPrimal3DBankReadout_eq_carrier
#print axioms CriticalLinePhasor.GlobalHelix.cpsPrimal3DBankReadout_independent_of_satake
