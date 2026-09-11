# Native carrier proof threading

Target attempted: `RiemannHypothesis`, with no additional arguments.
The existing bridge reduces its standard zeta-zero statement to
`∀ rho ∈ ZD.NontrivialZeros, rho.re = 1 / 2`, where membership means
`0 < rho.re ∧ rho.re < 1 ∧ riemannZeta rho = 0`.

The three existing inputs were tested directly, rather than adding a new
proposition to the target signature. Source and complete compiler diagnostics:
`NativeCarrierThreadAttempts20260909.lean` and
`NativeCarrierThreadAttempts20260909.txt` in this directory.
`lake env lean proof-drafts/NativeCarrierThreadAttempts20260909.lean` exited 1.

1. Log correspondence: the native height proves `rho.im = log sourceHeight`;
   the receiving input is `-I * (rho - 1/2) = log sourceHeight`.
2. Eigenvalue correspondence: the native event proves an eigenvector equation
   with scalar `rho.im`; the receiving input has scalar `-I * (rho - 1/2)`.
3. Analytic operator: its exact eigenvalue matches the door after the proved
   scalar rewrite. The remaining type mismatch is symmetry of
   `xiZeroLedgerNoDriftProjection` versus symmetry of `xiZeroLedgerOperator`.
   The final diagnostics contain only these three mismatches.

Backing up to the actual constructed maps, `RequestProject/NativeCarrierTransport.lean`
proves the following without a zero-location or symmetry hypothesis:

- The native event's basis mode is exactly `zeroHeightCorrespondence (single rho 1)`.
- That mode is nonzero and is an eigenvector of the carrier operator at `rho.im`.
- Transport of the analytic ledger eigenvector has scalar `-I * (rho - 1/2)`.
- Subtracting these two actions on the native mode gives
  `I * (rho.re - 1/2) • nativeMode rho`.
- On all finitely supported states, `K.comp A = H.comp K - I • K.comp D`,
  using the existing analytic operator decomposition and height intertwining.

Thus the two constructors have been connected explicitly. No theorem asserting
that this residual vanishes, and no theorem asserting `RiemannHypothesis`, is
claimed by this change.

`lake env lean RequestProject/NativeCarrierTransport.lean` exited 0.
`lake build RequestProject.NativeCarrierTransport` exited 0, with final output:

```text
Build completed successfully (8803 jobs).
```

Literal final declaration audit:

```text
'CriticalLinePhasor.NativeCarrierTransport.full_operator_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

The six other printed declarations have the same three axioms.
`rg -n 'axiom |sorry|admit|@\[implemented_by\]' RequestProject/NativeCarrierTransport.lean`
found no matches. Existing project theorem statements were not modified.

## Searches used

```sh
rg -n 'xiZeroLedgerOperator.*IsSymmetric|IsSymmetric.*xiZeroLedgerOperator|xiRadialDriftOperator = 0|xiZeroLedgerOperator = xiCarrierHeightOperator' RequestProject --glob '*.lean'
rg -n 'principalZero.*(eigen|Eigen|correspond|Correspond)|native.*[Ee]igenvalue|xiZeroLedgerOperator_isSymmetric|carrier.*poleParam|poleParam.*carrier|full.*[Ii]ntertwining' RequestProject --glob '*.lean'
rg -n '(:|→|↔) RiemannHypothesis|:.*IsSymmetric|:.*AllNative3DSourceTransfer' RequestProject --glob '*.lean'
rg -n 'fieldMarkers_drift_zero|helixDeprojectionCorrection_admissible|vonMangoldtEnvelopeBoundedObligation|scaleBoundedAtEveryZero|radialMagnitude.*[Bb]ound|[Bb]ound.*radialMagnitude' RequestProject --glob '*.lean'
rg -n 'poleParam_eq|def poleParam|hasEigenvalue.*hasEigenvector|hasEigenvector.*hasEigenvalue' RequestProject .lake/packages/mathlib/Mathlib/LinearAlgebra/Eigenspace --glob '*.lean'
rg -n 'HasEigenvalue|has_eigenvalue|hasEigenvalue|HasEigenvector|hasEigenvector|IsSymmetric|is_symmetric' .lake/packages/mathlib/Mathlib/LinearAlgebra/Eigenspace/Basic.lean .lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Symmetric.lean
rg -n 'theorem comp_smul|lemma comp_smul|theorem comp_sub|lemma comp_sub' .lake/packages/mathlib/Mathlib/Algebra/Module/LinearMap --glob '*.lean'
```

The prior constructor and axiom audit is preserved in
`HelixCorrespondenceAudit20260909.lean` and its corresponding output file.
