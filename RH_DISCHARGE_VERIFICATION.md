# RH/GRH draft verification

The September 7 source audit, support-module checks, and deliberate draft failures are in
[proof-drafts/2026-09-07/VERIFICATION.md](/Users/samuellavery/work/helix_frobenius/proof-drafts/2026-09-07/VERIFICATION.md).
The earlier verification is preserved below and in the
[before-review snapshot](/Users/samuellavery/work/helix_frobenius/proof-drafts/2026-09-07-before-review/RH_DISCHARGE_VERIFICATION.md).

## September 5 afternoon verification

The three support modules below passed their direct compiler gates. Their printed declarations use exactly `[propext, Classical.choice, Quot.sound]`. The four fixed-conclusion RH/GRH drafts still contain named unfinished leaves.

The earlier audit remains at [the archived early-morning verification](/Users/samuellavery/work/helix_frobenius/proof-drafts/2026-09-05-early/RH_DISCHARGE_VERIFICATION.md).

## RegistrationCalibration.lean

Command: `lake env lean RequestProject/RegistrationCalibration.lean`

Exit code: `0`.

Source SHA-256: `e998b73003e2fcf5a416797d65edbe371159733eb85455a033553aecef8e78c4`.

```text
warning: PrimeNumberTheoremAnd: repository '/Users/samuellavery/work/helix_frobenius/.lake/packages/PrimeNumberTheoremAnd' has local changes
'CriticalLinePhasor.ContourArgument.boundaryStation_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'CriticalLinePhasor.ContourArgument.boundary_resid_integer' depends on axioms: [propext, Classical.choice, Quot.sound]
'CriticalLinePhasor.ContourArgument.calibrated_registry_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CriticalLinePhasor.ContourArgument.offLine_increment_eq_registrationDefect_sub_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## SeatDegreeTwo.lean

Command: `lake env lean RequestProject/SeatDegreeTwo.lean`

Exit code: `0`.

Source SHA-256: `b08206ddc24170cf9c8eaf807954c8ffbaa98bce29b53451f435221f8ac5c3b1`.

```text
warning: PrimeNumberTheoremAnd: repository '/Users/samuellavery/work/helix_frobenius/.lake/packages/PrimeNumberTheoremAnd' has local changes
'CriticalLinePhasor.ContourArgument.SeatDegreeTwo.entries' depends on axioms: [propext, Classical.choice, Quot.sound]
'CriticalLinePhasor.ContourArgument.SeatDegreeTwo.block_primeMoment_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CriticalLinePhasor.ContourArgument.SeatDegreeTwo.det_re' depends on axioms: [propext, Classical.choice, Quot.sound]
'CriticalLinePhasor.ContourArgument.SeatDegreeTwo.det_nonneg_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CriticalLinePhasor.ContourArgument.SeatDegreeTwo.prime_det_re' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CriticalLinePhasor.ContourArgument.SeatDegreeTwo.prime_det_nonneg_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## StripTraceRegularCorrection.lean

Command: `lake env lean RequestProject/StripTraceRegularCorrection.lean`

Exit code: `0`.

Source SHA-256: `2906c6882b650ee13becd162e7100ff2e0ce74f46b04156aefda69295276c64e`.

```text
warning: PrimeNumberTheoremAnd: repository '/Users/samuellavery/work/helix_frobenius/.lake/packages/PrimeNumberTheoremAnd' has local changes
'CriticalLinePhasor.CaptureInterfaceAudit.normalizedLTrace_not_regular_correction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CriticalLinePhasor.CaptureInterfaceAudit.grh_of_regularCorrectionTraceLimit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## Dependency builds

Command: `lake build RequestProject.RegistrationFlux RequestProject.RegistrationScale RequestProject.StripTraceLimitIff RequestProject.RegistrationSeq RequestProject.LaplacePower`

Exit code: `0`. Final output line, verbatim:

```text
Build completed successfully (9570 jobs).
```

[Full build output](/Users/samuellavery/work/helix_frobenius/proof-drafts/2026-09-05-afternoon/latest-updates-build.log).

Command: `lake build RequestProject.RegistrationCalibration RequestProject.SeatDegreeTwo RequestProject.StripTraceRegularCorrection RequestProject.HelixHubFusion`

Exit code: `0`. Final output line, verbatim:

```text
Build completed successfully (9580 jobs).
```

[Full build output](/Users/samuellavery/work/helix_frobenius/proof-drafts/2026-09-05-afternoon/support-build.log).

## Source scan

```sh
rg -n 'axiom |sorry|admit|@\[implemented_by\]' RequestProject/RegistrationCalibration.lean RequestProject/SeatDegreeTwo.lean RequestProject/StripTraceRegularCorrection.lean
```

Exit code: `1`; no matching lines. The printed axiom footprints above also check their transitive theorem dependencies.

## Current dependency axiom audit

Command: `lake env lean /private/tmp/rh-afternoon-probes/Audit.lean`

Exit code: `0`.

[Exact audit input](/Users/samuellavery/work/helix_frobenius/proof-drafts/2026-09-05-afternoon/Audit.lean.txt). All 16 printed footprints are standard. Output, verbatim:

```text
warning: PrimeNumberTheoremAnd: repository '/Users/samuellavery/work/helix_frobenius/.lake/packages/PrimeNumberTheoremAnd' has local changes
'CriticalLinePhasor.ContourArgument.count_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
'CriticalLinePhasor.ContourArgument.S_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
'CriticalLinePhasor.ContourArgument.rieszRemainder_intervalIntegrable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CriticalLinePhasor.ContourArgument.registry_regClock_tendsto' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CriticalLinePhasor.ContourArgument.registry_gap_count' depends on axioms: [propext, Classical.choice, Quot.sound]
'CriticalLinePhasor.ContourArgument.registry_bankChange_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'CriticalLinePhasor.ContourArgument.boundaryTerm_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'CriticalLinePhasor.ContourArgument.boundaryTerm_split' depends on axioms: [propext, Classical.choice, Quot.sound]
'CriticalLinePhasor.ContourArgument.far_weights_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'CriticalLinePhasor.ContourArgument.contour_registrationHelix_third_gap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CriticalLinePhasor.CaptureInterfaceAudit.riemannHypothesis_of_integratedDefectSublinear' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CriticalLinePhasor.ContourArgument.rh_iff_prime_jets_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'CriticalLinePhasor.ContourArgument.PrimeClock.primeJetsForm_eq_dc_add_phase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CriticalLinePhasor.XiKernelBridge.xiArithmeticStage_mass_tendsto' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CriticalLinePhasor.SeatingLedger.riemannHypothesis_of_stage_mass' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CriticalLinePhasor.CaptureInterfaceAudit.stripTraceLimit_iff_GRH' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## Four unfinished proof leaves

Command: `lake env lean /private/tmp/rh-afternoon-probes/DraftProbes.lean`

Exit code: `1`, expected: exactly the four explicit `fail` commands shown below. There are no other compiler errors. These are incomplete drafts, not completed RH/GRH proofs.

[Exact combined probe input](/Users/samuellavery/work/helix_frobenius/proof-drafts/2026-09-05-afternoon/DraftProbes.lean.txt). It contains the four import/example blocks from the current draft document, isolated in namespaces. Output, verbatim:

```text
warning: PrimeNumberTheoremAnd: repository '/Users/samuellavery/work/helix_frobenius/.lake/packages/PrimeNumberTheoremAnd' has local changes
/private/tmp/rh-afternoon-probes/DraftProbes.lean:17:2: error: A: integrated bound for the full Riesz-minus-native balance, retaining multiplicity and bank change
⊢ (fun T => ∫ (t : ℝ) in 0..T, ↑(offLineStripZeroCountMult t)) =o[atTop] fun T => T
/private/tmp/rh-afternoon-probes/DraftProbes.lean:33:2: error: B: nonnegativity of the full DC plus correlated prime-power phase sum
γ σ : ℝ
hσ : 1 < σ
hσupper : σ < 3 / 2
R : Polynomial ℂ
hR : R.coeff 0 = 0
⊢ 0 ≤
    PrimeClock.dcForm R (↑σ + ↑γ * I) ↑(2 * σ - 1) +
      ∑' (n : ℕ),
        ArithmeticFunction.vonMangoldt n * ↑n ^ (-σ) *
          (PrimeClock.phase γ (Real.log ↑n) * PrimeClock.primeSymbol R (2 * σ - 1) (Real.log ↑n)).re
/private/tmp/rh-afternoon-probes/DraftProbes.lean:48:2: error: C: eventual theta-stage mass sign at this channel point
A : ℝ
hA : 0 < A
hdoor :
  (∀ (s : ℂ),
      1269 / 2 < |s.im| →
        A / Real.log |s.im| ^ 9 < s.re →
          s.re < 1 / 2 →
            ZD.riemannXi s ≠ 0 →
              ∃ G,
                Tendsto (fun n => G n s) atTop (𝓝 (ZD.riemannXi s)) ∧
                  Tendsto (fun n => deriv (G n) s) atTop (𝓝 (deriv ZD.riemannXi s)) ∧
                    ∀ᶠ (n : ℕ) in atTop, 0 ≤ (logDeriv (G n) s).re / (s.re - 1 / 2)) →
    RiemannHypothesis
s : ℂ
him : 1269 / 2 < |s.im|
hlo : A / Real.log |s.im| ^ 9 < s.re
hhi : s.re < 1 / 2
hxi : ZD.riemannXi s ≠ 0
⊢ ∀ᶠ (n : ℕ) in atTop, 0 ≤ (logDeriv ((fun n => xiArithmeticStage ↑n) n) s).re / (s.re - 1 / 2)
/private/tmp/rh-afternoon-probes/DraftProbes.lean:67:2: error: D: arithmetic finite spectra, correction regular through the real axis, and local uniform limit
N : ℕ
inst✝ : NeZero N
χ : DirichletCharacter ℂ N
⊢ ∃ r d c E,
    DifferentiableOn ℂ E spectralStrip ∧
      TendstoLocallyUniformlyOn (fun n => normalizedSpectrumTrace (d n) (c n)) (fun z => normalizedLTrace χ z - E z)
        atTop stripOffReal
```

## Search and artifact checks

The unfolded-identifier search output is [recorded here](/Users/samuellavery/work/helix_frobenius/proof-drafts/2026-09-05-afternoon/unfolded-search.log); the Mathlib search output is [recorded here](/Users/samuellavery/work/helix_frobenius/proof-drafts/2026-09-05-afternoon/mathlib-search.log). Commands and semantic queries are listed in the draft document and support-source headers.

All local draft links resolve, code fences balance, and the four final signatures remain `example : RiemannHypothesis` or `example : GRHSpectral.GRHComplete` with no added hypothesis binders. The supporting conditional lemmas retain their stated geometric and analytic conditions.
