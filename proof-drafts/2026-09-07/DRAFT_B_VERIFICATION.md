# Draft B verification

## Existing-theorem audit

```sh
lake env lean proof-drafts/2026-09-07/DraftBAudit.lean > /private/tmp/draft-b-audit.log 2>&1
```

Tool result: `"exit_code": 0`. Verbatim output:

```text
warning: PrimeNumberTheoremAnd: repository '/Users/samuellavery/work/helix_frobenius/.lake/packages/PrimeNumberTheoremAnd' has local changes
'CriticalLinePhasor.SeatingLedger.stage_bound_of_polynomial_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CriticalLinePhasor.SeatingLedger.explicitCoeff_polynomial_bound_of_stage_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CriticalLinePhasor.SeatingLedger.explicit_growth_unconditional' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CriticalLinePhasor.ContourArgument.PrimeClock.logMul_iterate_term' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CriticalLinePhasor.ContourArgument.PrimeClock.term_eq_weight_phase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## Support module build

```sh
lake build RequestProject.DraftBPrimeStages > /private/tmp/draft-b-prime-stages-build.log 2>&1
```

Tool result: `"exit_code": 0`. Verbatim closing output:

```text
ℹ [9573/9573] Built RequestProject.DraftBPrimeStages (346s)
info: RequestProject/DraftBPrimeStages.lean:161:0: 'CriticalLinePhasor.SeatingLedger.primeCoeffStage_succ_closed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: RequestProject/DraftBPrimeStages.lean:162:0: 'CriticalLinePhasor.SeatingLedger.anchorEndCoeff_succ' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RequestProject/DraftBPrimeStages.lean:163:0: 'CriticalLinePhasor.SeatingLedger.pairedPrimeStageCoeff_succ_closed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: RequestProject/DraftBPrimeStages.lean:164:0: 'CriticalLinePhasor.SeatingLedger.pairedPrimeStageCoeff_zero_closed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: RequestProject/DraftBPrimeStages.lean:165:0: 'CriticalLinePhasor.SeatingLedger.anchor_primeTerm_phase' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RequestProject/DraftBPrimeStages.lean:166:0: 'CriticalLinePhasor.SeatingLedger.explicitCoeffStage_eventually_exponential' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
Build completed successfully (9573 jobs).
```

## Majorant attempt

```sh
lake env lean proof-drafts/2026-09-07/DraftBMajorantAttempt.lean > /private/tmp/draft-b-majorant-attempt.log 2>&1
```

Tool result: `"exit_code": 1`. Verbatim output:

```text
warning: PrimeNumberTheoremAnd: repository '/Users/samuellavery/work/helix_frobenius/.lake/packages/PrimeNumberTheoremAnd' has local changes
proof-drafts/2026-09-07/DraftBMajorantAttempt.lean:20:6: error: linarith failed to find a contradiction
C : ℝ
hC : ∀ (k : ℕ), ‖toeplitzCoeff (-3) (jets explicitLogDeriv anchor20) k‖ ≤ C * growthBase ^ k
k : ℕ
hlt : ‖toeplitzCoeff (-3) (jets explicitLogDeriv anchor20) k‖ < C * growthBase ^ k + 1
hev : ∀ᶠ (a : ℕ) in atTop, ‖explicitCoeffStage a k‖ < C * growthBase ^ k + 1
N : ℕ
hN : ‖explicitCoeffStage N k‖ < C * growthBase ^ k + 1
a✝ : (C + 1) * (1 + 1) < C * growthBase ^ k + 1
⊢ False
failed
```

## Convergence attempt

```sh
lake env lean proof-drafts/2026-09-07/DraftBConvergenceAttempt.lean > /private/tmp/draft-b-convergence-attempt.log 2>&1
```

Tool result: `"exit_code": 1`. The preceding convergence and limit-transfer
steps elaborated; the last search for the common polynomial envelope did not close.
Verbatim output:

```text
warning: PrimeNumberTheoremAnd: repository '/Users/samuellavery/work/helix_frobenius/.lake/packages/PrimeNumberTheoremAnd' has local changes
proof-drafts/2026-09-07/DraftBConvergenceAttempt.lean:21:2: error: `exact?` could not close the goal. Try `apply?` to see partial suggestions.
```

The remaining goal's source is the `suffices` statement at line 17, with
`B k = ‖toeplitzCoeff (-3) (jets explicitLogDeriv anchor20) k‖ + 1`.

## Direct support check

```sh
lake env lean RequestProject/DraftBPrimeStages.lean > /private/tmp/draft-b-prime-stages-final.log 2>&1
```

Tool result: `"exit_code": 0`. Verbatim output:

```text
warning: PrimeNumberTheoremAnd: repository '/Users/samuellavery/work/helix_frobenius/.lake/packages/PrimeNumberTheoremAnd' has local changes
'CriticalLinePhasor.SeatingLedger.primeCoeffStage_succ_closed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CriticalLinePhasor.SeatingLedger.anchorEndCoeff_succ' depends on axioms: [propext, Classical.choice, Quot.sound]
'CriticalLinePhasor.SeatingLedger.pairedPrimeStageCoeff_succ_closed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CriticalLinePhasor.SeatingLedger.pairedPrimeStageCoeff_zero_closed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CriticalLinePhasor.SeatingLedger.anchor_primeTerm_phase' depends on axioms: [propext, Classical.choice, Quot.sound]
'CriticalLinePhasor.SeatingLedger.explicitCoeffStage_eventually_exponential' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## Paired attempt

```sh
lake env lean proof-drafts/2026-09-07/DraftBPairedAttempt.lean > /private/tmp/draft-b-paired-attempt-final.log 2>&1
```

Tool result: `"exit_code": 1`. Exactly one error remains, at the final estimate.
The finite-part case, common-constant enlargement, and positive-degree
rewriting elaborated. Verbatim output:

```text
warning: PrimeNumberTheoremAnd: repository '/Users/samuellavery/work/helix_frobenius/.lake/packages/PrimeNumberTheoremAnd' has local changes
proof-drafts/2026-09-07/DraftBPairedAttempt.lean:44:2: error: `exact?` could not close the goal. Try `apply?` to see partial suggestions.
⊢ ∃ C p,
    ∀ (k : ℕ),
      ∀ᶠ (N : ℕ) in atTop,
        ‖archRemainderCoeff (k + 1) +
              (anchor20⁻¹ ^ 2 * transport anchor20 0 ^ k +
                ∑ n ∈ range N, LSeries.term vonMangoldtC (1 - anchor20) n * primeCoeffSymbol (-3) k (Real.log ↑n))‖ ≤
          C * (1 + ↑(k + 1) ^ p)
```

## Source checks

```sh
rg -n 'axiom |sorry|admit|@\[implemented_by\]' RequestProject/DraftBPrimeStages.lean proof-drafts/2026-09-07/DraftB*.lean
```

Tool result: `"exit_code": 1`, empty output: no matches. The failed examples
are outside the library module; no completed theorem is exported from them.

```sh
git diff --check
```

Tool result: `"exit_code": 0`, empty output.

SHA-256 source snapshot:

```text
2d4febb3b388db77c7a8cd2d969114cbcd57dd19895d218b97db963d54d7ee5b  RequestProject/DraftBPrimeStages.lean
1fc28cba3921d814d4784238e3699d85545ae49ead254faced9799a405c3a326  proof-drafts/2026-09-07/DraftBAudit.lean
d850dff373bf9c6ae16d807c8a79878eb3be318b94dcfeb6a2cbd592b935c7e4  proof-drafts/2026-09-07/DraftBMajorantAttempt.lean
238158d5dbb12a0bf95a5163b1edd32f8378bdf7308489f7af125cdf481feb37  proof-drafts/2026-09-07/DraftBConvergenceAttempt.lean
443bf7ae960b67c5cdea17f59e4eb46f7a0d1eae71db61f694c96129b6fa09fb  proof-drafts/2026-09-07/DraftBPairedAttempt.lean
```
