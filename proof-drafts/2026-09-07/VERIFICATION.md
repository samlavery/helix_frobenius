# September 7 verification

The audit covers the latest `GrowthGap` addition, the explicit-anchor chain it imports,
and the GRH regular-correction trace consumer used by Draft D.

## Recent dependency audit

```sh
lake build RequestProject.GrowthGap RequestProject.StripTraceRegularCorrection > /private/tmp/sep7-recent-build.log 2>&1
```

Tool result: `"exit_code": 0`. Verbatim closing build output:

```text
 Quot.sound]
ℹ [9559/9560] Replayed RequestProject.StripTraceRegularCorrection
info: RequestProject/StripTraceRegularCorrection.lean:58:0: 'CriticalLinePhasor.CaptureInterfaceAudit.normalizedLTrace_not_regular_correction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: RequestProject/StripTraceRegularCorrection.lean:59:0: 'CriticalLinePhasor.CaptureInterfaceAudit.grh_of_regularCorrectionTraceLimit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
ℹ [9560/9560] Replayed RequestProject.GrowthGap
info: RequestProject/GrowthGap.lean:131:0: 'CriticalLinePhasor.SeatingLedger.norm_transport_anchor_le' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RequestProject/GrowthGap.lean:132:0: 'CriticalLinePhasor.SeatingLedger.explicit_growth_unconditional' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: RequestProject/GrowthGap.lean:133:0: 'CriticalLinePhasor.SeatingLedger.explicit_growth_unconditional'' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: RequestProject/GrowthGap.lean:134:0: 'CriticalLinePhasor.SeatingLedger.growthBase_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (9560 jobs).
```

## Support module

`ExplicitAnchorDischarge.lean` contains completed support lemmas. The executable
drafts remain unfinished and are checked separately.

```sh
lake build RequestProject.ExplicitAnchorDischarge > /private/tmp/sep7-support-build.log 2>&1
```

Tool result: `"exit_code": 0`. Verbatim closing build output:

```text
⚠ [9559/9559] Built RequestProject.ExplicitAnchorDischarge (323s)
warning: RequestProject/ExplicitAnchorDischarge.lean:40:12: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
info: RequestProject/ExplicitAnchorDischarge.lean:133:0: 'CriticalLinePhasor.SeatingLedger.primeJetStage_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RequestProject/ExplicitAnchorDischarge.lean:134:0: 'CriticalLinePhasor.SeatingLedger.explicitCoeffStage_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RequestProject/ExplicitAnchorDischarge.lean:135:0: 'CriticalLinePhasor.SeatingLedger.riemannHypothesis_of_explicit_stage_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: RequestProject/ExplicitAnchorDischarge.lean:136:0: 'CriticalLinePhasor.SeatingLedger.riemannHypothesis_of_explicit_rates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: RequestProject/ExplicitAnchorDischarge.lean:137:0: 'CriticalLinePhasor.SeatingLedger.one_lt_growthBase' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (9559 jobs).
```

Final-source direct check:

```sh
lake env lean RequestProject/ExplicitAnchorDischarge.lean > /private/tmp/sep7-anchor-discharge-final.log 2>&1
```

Tool result: `"exit_code": 0`. Verbatim full output:

```text
warning: PrimeNumberTheoremAnd: repository '/Users/samuellavery/work/helix_frobenius/.lake/packages/PrimeNumberTheoremAnd' has local changes
RequestProject/ExplicitAnchorDischarge.lean:40:12: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
'CriticalLinePhasor.SeatingLedger.primeJetStage_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound]
'CriticalLinePhasor.SeatingLedger.explicitCoeffStage_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound]
'CriticalLinePhasor.SeatingLedger.riemannHypothesis_of_explicit_stage_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CriticalLinePhasor.SeatingLedger.riemannHypothesis_of_explicit_rates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CriticalLinePhasor.SeatingLedger.one_lt_growthBase' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Executable drafts

```sh
lake env lean proof-drafts/2026-09-07/DischargeDrafts.lean > /private/tmp/sep7-discharge-drafts.log 2>&1
```

Tool result: `"exit_code": 1`. Exactly four errors, each from an intentional
`fail` after the preceding construction has elaborated. No import, type, or
unknown-identifier errors occur. These drafts have not proved RH or GRH.

Verbatim full output (Lean prints each traced remaining goal twice):

```text
warning: PrimeNumberTheoremAnd: repository '/Users/samuellavery/work/helix_frobenius/.lake/packages/PrimeNumberTheoremAnd' has local changes
proof-drafts/2026-09-07/DischargeDrafts.lean:18:2: error: Draft A: construct C and p and prove the polynomial bound for every degree
⊢ ∃ C p, ∀ (k : ℕ), ‖toeplitzCoeff (-3) (jets explicitLogDeriv (-1 + 20 * I)) k‖ ≤ C * (1 + ↑k ^ p)
⊢ ∃ C p, ∀ (k : ℕ), ‖toeplitzCoeff (-3) (jets explicitLogDeriv (-1 + 20 * I)) k‖ ≤ C * (1 + ↑k ^ p)
proof-drafts/2026-09-07/DischargeDrafts.lean:24:2: error: Draft B: construct C and p independent of degree and cutoff; prove the eventual stage bound
⊢ ∃ C p, ∀ (k : ℕ), ∀ᶠ (N : ℕ) in atTop, ‖explicitCoeffStage N k‖ ≤ C * (1 + ↑k ^ p)
⊢ ∃ C p, ∀ (k : ℕ), ∀ᶠ (N : ℕ) in atTop, ‖explicitCoeffStage N k‖ ≤ C * (1 + ↑k ^ p)
proof-drafts/2026-09-07/DischargeDrafts.lean:33:2: error: Draft C: construct the complete rate family and prove every rate's every-degree bound
⊢ ∃ b C,
    (∀ (j : ℕ), 0 ≤ b j) ∧
      Tendsto b atTop (𝓝 1) ∧ ∀ (j k : ℕ), ‖toeplitzCoeff (-3) (jets explicitLogDeriv anchor20) k‖ ≤ C j * b j ^ k
⊢ ∃ b C,
    (∀ (j : ℕ), 0 ≤ b j) ∧
      Tendsto b atTop (𝓝 1) ∧ ∀ (j k : ℕ), ‖toeplitzCoeff (-3) (jets explicitLogDeriv anchor20) k‖ ≤ C j * b j ^ k
proof-drafts/2026-09-07/DischargeDrafts.lean:48:2: error: Draft D: construct arithmetic spectra and the trace limit with a regular correction
N : ℕ
inst✝ : NeZero N
χ : DirichletCharacter ℂ N
⊢ ∃ r d c E,
    DifferentiableOn ℂ E spectralStrip ∧
      TendstoLocallyUniformlyOn (fun n => normalizedSpectrumTrace (d n) (c n)) (fun z => normalizedLTrace χ z - E z)
        atTop stripOffReal
N : ℕ
inst✝ : NeZero N
χ : DirichletCharacter ℂ N
⊢ ∃ r d c E,
    DifferentiableOn ℂ E spectralStrip ∧
      TendstoLocallyUniformlyOn (fun n => normalizedSpectrumTrace (d n) (c n)) (fun z => normalizedLTrace χ z - E z)
        atTop stripOffReal
```

## Source checks

```sh
rg -n 'axiom |sorry|admit|@\[implemented_by\]' RequestProject/GrowthGap.lean RequestProject/ExplicitAnchorDischarge.lean proof-drafts/2026-09-07/DischargeDrafts.lean
```

Tool result: `"exit_code": 1`, empty output: no matches. The four `fail` tactics
in the draft file produce errors; they do not admit declarations into the kernel.

```sh
git diff --check
```

Tool result: `"exit_code": 0`, empty output.

SHA-256 source snapshot:

```text
f91118875330b6fcf3258c5c00e5a3f525a33d86dae6f43cd7a4095d91844d50  RequestProject/GrowthGap.lean
82f0bfa204d38a950a6aac18bbde6e1ce3f5fba02e1c1b890845ae97cd0ede75  RequestProject/ExplicitAnchorDischarge.lean
2906c6882b650ee13becd162e7100ff2e0ce74f46b04156aefda69295276c64e  RequestProject/StripTraceRegularCorrection.lean
f631b0ee6fd7070def4675acde37866eaab437c21cf57058bc03909d444da833  proof-drafts/2026-09-07/DischargeDrafts.lean
```

## Search record

The source header unfolds the coefficient and stage definitions. The following
searches preceded the construction, in addition to reading `GrowthGap`,
`ExplicitAnchor`, `SubexponentialAnchor`, and the two strip-trace modules:

```sh
rg -n -i 'prime_?jet_?stage|primeJetStage|anchor_?coeff_?stage|stage_?coefficient|coeff.*tendsto|tendsto.*coeff|normalized.*decay|rates.*tendsto|exp.*bound.*one' RequestProject --glob '*.lean'
rg -n 'LSeriesSummable.*abscissa|LSeriesSummable.*iff|tendsto_sum_nat|le_of_tendsto|abscissaOfAbsConv_logMul' .lake/packages/mathlib/Mathlib --glob '*.lean'
rg -n 'theorem lt_sqrt|theorem one_lt_sqrt|lemma lt_sqrt' .lake/packages/mathlib/Mathlib/Analysis/Real/Sqrt.lean
```

Semantic searches: LeanSearch for passing an eventual upper bound to a real limit;
Loogle `Filter.Tendsto, (_ ≤ _)`. The resulting `le_of_tendsto` is used directly.
The local source also supplied `LSeries.absicssaOfAbsConv_logPowMul`,
`LSeriesSummable_of_abscissaOfAbsConv_lt_re`, `HasSum.tendsto_sum_nat`, and
`tendsto_finsetSum`.

The earlier prose and verification were preserved in `../2026-09-07-before-review/`
before the root index documents were updated. No older Lean declaration was changed.
