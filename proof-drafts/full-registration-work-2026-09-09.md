# Full-proof construction record

The fixed target is `RiemannHypothesis`, with no added arguments. Its definition in
Mathlib/NumberTheory/LSeries/RiemannZeta.lean:185 is:

```lean
∀ (s : ℂ), riemannZeta s = 0 →
  (¬ ∃ n : ℕ, s = -2 * (n + 1)) → s ≠ 1 → s.re = 1 / 2
```

In plain mathematics: every zero other than a negative even integer and the excluded
point 1 has real part one half. The carrier construction is intended to supply that
real part through identification with the balanced carrier readout.

## Unfolded register route

The chosen downstream theorem is `DVP.rh_of_smultIntegralSublinear`.
Its input, unfolded, is: for every positive epsilon, for all sufficiently large T,

    -epsilon * T ≤ integral from 0 to T of [N_on,mult(t) - 1 - theta(t)/pi].

The known Littlewood bound concerns `SAll = Smult + N_off,mult`.
The carrier coordinate is t = log Z, and hence the same integral is

    integral from 1 to exp T of Smult(log Z) / Z dZ.

The event height Z is distinct from the growth head `physicalHead t`.
Local pole cancellation in `WarpNoResidue` uses front parameter
`log (physicalHead t)`. It does not replace t by that front parameter in the census.

## Search record

Commands actually run, in addition to the source-reading searches in the earlier
session records:

```sh
rg -n 'fieldMarkers_drift_zero|helixDeprojectionCorrection_admissible|vonMangoldtEnvelopeBoundedObligation|nativeZetaZeros_re_eq_halfUnit_iff' . --glob '*.lean' --glob '!.lake/**' --glob '!proof-drafts/**' --glob '!tmp/**'
rg -n 'globalCoordinateIdentification|integral_sublinear|smultIntegralSublinear|radialResidue.*zero|registration.*holds|Registration.*holds' RequestProject --glob '*.lean'
rg -n 'Smult.*(bound|nonneg|[Ss]ublinear)|smult.*(lower|[Nn]onneg|[Ss]ublinear)|integral.*Smult|Smult.*integral|[Rr]egister.*[Ll]ower' RequestProject --glob '*.lean'
rg -n 'integral_comp_log|integral_log_mul|integral_comp_exp|integral_exp_mul|integral_comp_mul_deriv|integral_comp.*deriv' .lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral*
rg -n 'integral.*(logHeight|log_height|log Z)|integral_logHeight|smultIntegralSublinear|SmultIntegralSublinear|offLineStripZeroCountMult|RiemannHypothesis' .lake/packages/mathlib/Mathlib/NumberTheory/LSeries .lake/packages/mathlib/Mathlib/MeasureTheory/Integral --glob '*.lean'
```

Semantic searches actually called:

* LeanSearch: `interval integral substitution monotone differentiable function no continuity integrand`.
* Loogle: `"integral_comp_mul_deriv_of_deriv_nonneg"`.

The applicable substitution theorem exists and requires no continuity assumption on
the jump register. It is used with the increasing map exp, whose derivative is exp.

## Decompositions attempted with the fixed target

Without a prior expectation, I would first compose the exact register identities and
test which bound each available theorem supplies.

A. Littlewood plus the exact integral split. First Lean line:

```lean
apply rh_of_smultIntegralSublinear
```

B. Local cancellation plus the integrated correction-residue identity. First Lean line:

```lean
apply rh_of_smultIntegralSublinear
```

C. Back up to the bank's native/unit warp law and its multiplicity correction. The
internal step tested is:

```lean
have hregister : ∀ t : ℝ, SAll t = Smult t := by
  intro t
  have hwarp := CriticalLinePhasor.CarrierScale.carrier_scale_compensation_S t
  have hmult := Smult_sub_S t
  change Smult t + (offLineStripZeroCountMult t : ℝ) = Smult t
  linarith only [hwarp, hmult]
```

The combined import run was interrupted without a compiler result. The checks were
split into smaller imports. Strategies A and C are in
`FullRegistrationAttempts20260909.lean`; `lake env lean` exited 1, with both
`linarith` failures recorded verbatim in the matching `.txt`. In A, a nonnegative
correction integral has no upper bound supplied by the available inequalities. In C,
the carrier warp and multiplicity identities leave `Smult t + N_off t = Smult t`
unproved.

Strategy B's local obligation is isolated in
`LocalCancellationDischargeAttempt20260909.lean`. Its separate compiler invocation
was also interrupted before any Lean diagnostics or axiom output arrived; no completed
compiler result is claimed for B. These are proof-attempt files, not completed theorem
modules, and neither is imported into `RequestProject`.

## Constructed coordinate transport

`RequestProject/LogHeightRegistration.lean` proves the change of variables, its
integrability equivalence, the exact full/line register split in physical height,
Littlewood's bound in those coordinates, and the resulting lower bound with the
correction integral retained.

These statements preserve the existing `Smult`, `SAll`, and off-line count definitions.
They do not assert that the correction integral vanishes.

Verification of `LogHeightRegistration.lean`: `lake env lean
RequestProject/LogHeightRegistration.lean` exited 0. Its six printed axiom footprints
are recorded verbatim in `LogHeightRegistration20260909.txt`. A source scan for
`axiom |sorry|admit|@\[implemented_by\]` returned no matches.
