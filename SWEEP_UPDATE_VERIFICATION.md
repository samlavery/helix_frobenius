# Sweep update verification — 2026-09-06

## Updated dependency chain

Command executed from `/Users/samuellavery/work/helix_frobenius`:

```sh
lake build RequestProject.BoundedIffRH > /private/tmp/rh-sep6-latest-build.log 2>&1
```

Tool result: `"exit_code": 0`. Selected verbatim build output:

```text
info: RequestProject/HerglotzSweep.lean:193:0: 'CriticalLinePhasor.SeatingLedger.xiHerglotz_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RequestProject/JetsAreAtoms.lean:374:0: 'CriticalLinePhasor.SeatingLedger.toeplitzCoeff_jets_eq_xiCoeff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: RequestProject/JetsAreAtoms.lean:375:0: 'CriticalLinePhasor.SeatingLedger.explicit_ladder_iff_rh' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RequestProject/BoundedIffRH.lean:217:0: 'CriticalLinePhasor.SeatingLedger.explicit_bounded_iff_rh' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (9556 jobs).
```

## Sweep geometry and normalization

```sh
lake env lean RequestProject/SeatHerglotzSweep.lean > /private/tmp/seat-herglotz-sweep.log 2>&1
```

Tool result: `"exit_code": 0`. Complete verbatim output:

```text
warning: PrimeNumberTheoremAnd: repository '/Users/samuellavery/work/helix_frobenius/.lake/packages/PrimeNumberTheoremAnd' has local changes
RequestProject/SeatHerglotzSweep.lean:68:4: warning: Try `simp at hz` instead of `simpa using hz`

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
'CriticalLinePhasor.SeatingLedger.movedAnchor_inverse' depends on axioms: [propext, Classical.choice, Quot.sound]
'CriticalLinePhasor.SeatingLedger.xiHerglotz_re_eq_scaled_seatMass' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CriticalLinePhasor.SeatingLedger.hker_re_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'CriticalLinePhasor.SeatingLedger.Gclock_re_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Polynomial-growth extension and fixed-anchor consumer

```sh
lake env lean RequestProject/SubexponentialAnchor.lean > /private/tmp/subexponential-anchor.log 2>&1
```

Tool result: `"exit_code": 0`. Complete verbatim output:

```text
warning: PrimeNumberTheoremAnd: repository '/Users/samuellavery/work/helix_frobenius/.lake/packages/PrimeNumberTheoremAnd' has local changes
RequestProject/SubexponentialAnchor.lean:232:25: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
'CriticalLinePhasor.SeatingLedger.re_ge_half_of_subexponential' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CriticalLinePhasor.SeatingLedger.rh_of_subexponential' depends on axioms: [propext, Classical.choice, Quot.sound]
'CriticalLinePhasor.SeatingLedger.normalized_decay_of_polynomial_growth' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CriticalLinePhasor.SeatingLedger.rh_of_polynomial_growth' depends on axioms: [propext, Classical.choice, Quot.sound]
'CriticalLinePhasor.SeatingLedger.explicit_polynomial_growth_iff_rh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CriticalLinePhasor.SeatingLedger.riemannHypothesis_of_explicit_fixed_anchor_polynomial_growth' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## Source escape-hatch scan

```sh
rg -n 'axiom |sorry|admit|@\[implemented_by\]' RequestProject/HerglotzSweep.lean RequestProject/JetsAreAtoms.lean RequestProject/BoundedIffRH.lean RequestProject/AnchorLadder.lean RequestProject/LadderMinor.lean RequestProject/LadderImpliesRH.lean RequestProject/ExplicitAnchor.lean RequestProject/SubexponentialAnchor.lean RequestProject/SeatHerglotzSweep.lean
```

No output; tool result `"exit_code": 1` (no matches). The printed axiom footprints
above separately audit the transitive proofs of the named theorems.

## Additional searches for the arithmetic estimate

```sh
rg -n -i '(bounded|bound|growth|norm_le|summable).*(toeplitz|laguerre|prime_?jets|xi_?coeff)|((toeplitz|laguerre|prime_?jets|xi_?coeff).*(bounded|bound|growth|norm_le|summable))' RequestProject --glob '*.lean'
rg -n -i 'toeplitz|laguerre|li_?coeff|xi_?coeff|prime_?jets|riemann.*hypothesis' .lake/packages/mathlib/Mathlib/NumberTheory .lake/packages/mathlib/Mathlib/Analysis --glob '*.lean'
```

The relevant source headers retain the earlier geometric and asymptotic searches
and the unfolded statements. The new source files introduce no unconditional RH
or GRH theorem: their growth consumers retain the displayed arithmetic estimate.
