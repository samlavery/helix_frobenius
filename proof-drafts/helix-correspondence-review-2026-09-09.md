# Source and correspondence audit

The audit inspected the native analytic fiber and carrier event constructors,
the carrier operator, the analytic zero operator, the map between their mode
spaces, its discharge routes, and the recently added source predicates.
Existing project declarations were not edited.

## Verified construction

`ZetaZeroNative3DSourceTransfer.lean:67` constructs
`PrincipalZeroAnalyticFiber3D rho` from membership in `ZD.NontrivialZeros` alone.
It includes the actual eta-configured 3D fiber, convergence of its corrected
partial sums to zero, a positive height `exp rho.im`, and a nonzero ambient
eigenvector. Line 151 constructs `PrincipalZeroNativeCarrierEvent3D rho`.
Line 177 gives its ambient eigenvector equation, with eigenvalue `(rho.im : ℂ)`.

`ThreeDFocalEvent.lean:420` proves symmetry of the ambient carrier operator.
This is an actual geometric operator theorem.

## Correspondence traced through the operators

`HelixHeightCorrespondence.lean:35` constructs `zeroHeightCorrespondence` on
all finitely supported analytic-zero modes. Line 92 proves

```lean
zeroHeightCorrespondence.comp xiCarrierHeightOperator =
  (carrierThreeDOperator 1 1).comp zeroHeightCorrespondence
```

The source operator in that theorem is `xiCarrierHeightOperator`.
`XiZeroLedgerResolvent3D.lean:327` defines its diagonal as `rho.val.im`.
The analytic operator `xiZeroLedgerOperator`, defined at line 257, instead has
diagonal `HelixLimit.poleParam rho.val`.

For `rho = beta + I * gamma`, these coefficients are respectively
`gamma` and `gamma + I * (1/2 - beta)`.
The exact operator decomposition is compiled at line 339:

```lean
xiZeroLedgerOperator =
  xiCarrierHeightOperator - Complex.I • xiRadialDriftOperator
```

The first-moment identity on reflected pairs is proved at
`HelixHeightCorrespondence.lean:110`. The second-moment difference at line 121
retains the coefficient `-2 * (rho.val.re - 1/2)^2`.

`HelixHeightDischarge.lean:116` produces the full analytic intertwining from
an argument `hs : xiZeroLedgerOperator.IsSymmetric`. The unconditional symmetry
theorem found in the construction applies to `xiCarrierHeightOperator`.
The kernel-descent and Green-transport routes in the same file likewise take
their respective transport laws as arguments. The station-registration routes
take a `StationRegistration` or `PositiveStationRegistration` structure;
the inspected callers do not construct a global instance of either structure.

`HPCorrespondenceDoor.lean:51` consumes eigenvalue membership for the full
spectral parameter `-Complex.I * (rho - 1/2)` in one symmetric operator.
It does not require equality of scalar readout functions.

## Recently added source definition

`SourceIsCancellation.lean:63` defines `HasSource` using eventual nonvanishing
of the two *smoothed head-bank* sums and convergence of their difference.
The native analytic-fiber constructor above uses the eta-configured spectral
fiber and does not directly have this new predicate as its result type.
`RHSourceStatement.lean:26` takes both `EveryZeroHasSource` and
`SourcesOfZerosOnAxis` as arguments.

## Verification and search record

`lake env lean proof-drafts/HelixCorrespondenceAudit20260909.lean` exited 0.
It checks seven existing signatures and prints ten axiom footprints; all ten
are exactly the standard three. The literal output is preserved in
`proof-drafts/HelixCorrespondenceAudit20260909.txt`.

Representative executed searches:

```sh
rg -n 'HPCorrespondence|riemannHypothesis_of_log_correspondence|riemannHypothesis_of_eigenvalue_correspondence|SourcesOfZerosOnAxis|Source.HasSource|Source.EveryZeroHasSource' RequestProject --glob '*.lean'
rg -n 'AnalyticHeightIntertwining|heightIntertwining|height_intertwining|zeroHeightCorrespondence.comp xiZeroLedgerOperator|Semiconj zeroHeightCorrespondence' RequestProject --glob '*.lean'
rg -n 'StationRegistration.*where|PositiveStationRegistration.*where|: (Nonempty )?\(?PositiveStationRegistration|: (Nonempty )?\(?StationRegistration|semiconj_of_kernel_descent|semiconj_of_green_transport|semiconj_of_ledger_symmetric' RequestProject --glob '*.lean'
rg -n 'xiZeroLedgerOperator_isSymmetric|xiZeroLedgerOperator_symmetric|carrierScaleBalanced.*(holds|zero)|all.*Native3D.*(holds|proved)' RequestProject --glob '*.lean'
rg -n 'principalContourNative3DCertificate_of|PrincipalContourNative3DCertificate.*where|: PrincipalContourNative3DCertificate|Nonempty \(PrincipalContourNative3DCertificate' RequestProject --glob '*.lean'
```

The audit establishes that the source construction and height correspondence
are implemented. It did not locate an unconditional producer of the full
analytic eigenvalue correspondence in the inspected paths.
