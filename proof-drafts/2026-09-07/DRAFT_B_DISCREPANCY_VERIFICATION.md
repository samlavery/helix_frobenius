# Draft B: discrepancy estimates and boundary proof

The completed source is
[DraftBDiscrepancy.lean](/Users/samuellavery/work/helix_frobenius/RequestProject/DraftBDiscrepancy.lean).
Draft B's common polynomial envelope is not proved in this module.

Write `E(N) = sum_{n<N}(Lambda(n)-1)` and
`K_k(n) = n^(-2) exp(20 i log n) primeCoeffSymbol(-3,k,log n)`.
The file proves:

- `|E(N)| <= (log 4 + 5) N`, using Chebyshev's theorem.
- The exact Abel boundary identity, both by summation by parts and independently by induction.
- The finite discrepancy estimate in `|E(N)|` and the differences of the actual kernel.
- `K_k(N) E(N+1) -> 0` for each fixed degree, using `(log N)^m/N -> 0`.
- The stage remainder equals the bounded paired gamma coefficient, including at degree zero.
- A common constant `A >= 0` with, for each `k`, eventually in `N`,
  `|explicitCoeffStage (N+1) (k+1)| <= A + |primeDiscrepancyStage N k|`.

The last expression keeps the uniform-density term and the signed arithmetic
variation together inside one norm. Neither the cutoff nor the arithmetic
phase has been optimized separately by prime power. The definition retains
the actual phase `exp(20 i log n)` at every integer.

No estimate of the form

```lean
∃ C : ℝ, ∃ p : ℕ, ∀ k, ∀ᶠ N in atTop,
  ‖explicitCoeffStage N k‖ ≤ C * (1 + (k : ℝ) ^ p)
```

is asserted here. The original unconditional theorem signature remains the target.

## Direct compiler check

Working directory: `/Users/samuellavery/work/helix_frobenius`.

```sh
lake env lean RequestProject/DraftBDiscrepancy.lean
```

Exit code: `0`. Complete output, verbatim:

```text
warning: PrimeNumberTheoremAnd: repository '/Users/samuellavery/work/helix_frobenius/.lake/packages/PrimeNumberTheoremAnd' has local changes
'CriticalLinePhasor.SeatingLedger.primeMassError_abs_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'CriticalLinePhasor.SeatingLedger.primeMassError_abel_succ' depends on axioms: [propext, Classical.choice, Quot.sound]
'CriticalLinePhasor.SeatingLedger.pairedPrimeStageCoeff_discrepancy_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CriticalLinePhasor.SeatingLedger.pairedPrimeStageCoeff_chebyshev_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CriticalLinePhasor.SeatingLedger.primeMassError_kernel_boundary_tendsto_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CriticalLinePhasor.SeatingLedger.explicitCoeffStage_discrepancy_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CriticalLinePhasor.SeatingLedger.explicitCoeffStage_eventually_le_discrepancy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

Source SHA-256:

```text
76bd77b76052dfca03b4a0f2ac59b97d2c73a2c2fe618535c6a041ceec54b894  RequestProject/DraftBDiscrepancy.lean
```

Source scan:

```sh
rg -n 'axiom |sorry|admit|@\[implemented_by\]|exact\?' RequestProject/DraftBDiscrepancy.lean
```

Exit code: `1`, with no output (no matches).

## Isolated logarithmic-limit check

```sh
lake env lean /private/tmp/DraftBLogBoundary.lean
```

Exit code: `0`. Complete output, verbatim:

```text
warning: PrimeNumberTheoremAnd: repository '/Users/samuellavery/work/helix_frobenius/.lake/packages/PrimeNumberTheoremAnd' has local changes
'draftB_logMoment_div_nat' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The checked proof is inserted in `primeCoeffSymbol_div_nat_tendsto_zero` in the completed module.

## Module build

```sh
lake build RequestProject.DraftBDiscrepancy
```

Exit code: `0`. Final module output, verbatim (earlier dependency replay omitted):

```text
ℹ [9578/9578] Built RequestProject.DraftBDiscrepancy (226s)
info: RequestProject/DraftBDiscrepancy.lean:324:0: 'CriticalLinePhasor.SeatingLedger.primeMassError_abs_le' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RequestProject/DraftBDiscrepancy.lean:325:0: 'CriticalLinePhasor.SeatingLedger.primeMassError_abel_succ' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RequestProject/DraftBDiscrepancy.lean:326:0: 'CriticalLinePhasor.SeatingLedger.pairedPrimeStageCoeff_discrepancy_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: RequestProject/DraftBDiscrepancy.lean:327:0: 'CriticalLinePhasor.SeatingLedger.pairedPrimeStageCoeff_chebyshev_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: RequestProject/DraftBDiscrepancy.lean:328:0: 'CriticalLinePhasor.SeatingLedger.primeMassError_kernel_boundary_tendsto_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: RequestProject/DraftBDiscrepancy.lean:329:0: 'CriticalLinePhasor.SeatingLedger.explicitCoeffStage_discrepancy_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: RequestProject/DraftBDiscrepancy.lean:330:0: 'CriticalLinePhasor.SeatingLedger.explicitCoeffStage_eventually_le_discrepancy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
Build completed successfully (9578 jobs).
```
