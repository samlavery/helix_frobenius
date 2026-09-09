# Common-bound attempt: a uniform bound for the prime kernel

The requested bound for `explicitCoeffStage` is not proved:

```lean
∃ C : ℝ, ∃ p : ℕ, ∀ k, ∀ᶠ N in atTop,
  ‖explicitCoeffStage N k‖ ≤ C * (1 + (k : ℝ) ^ p)
```

`RequestProject/PrimeKernelUniformBound.lean` proves an unconditional bound for each
scalar prime symbol, uniformly over **every** degree. Write `r = exp(-3*ell/2)`.
For `ell > 0` the bound is

```text
|primeCoeffSymbol(-3,k,ell)| <= (1+r)/(3*r*(1-r)).
```

For `ell >= log 2` this gives `|primeCoeffSymbol(-3,k,ell)| <= exp(3*ell/2)`.
Consequently the symbol multiplied by `n^(-2)` has norm at most `n^(-1/2)` for
every natural `k` and `n >= 2`.

The proof extracts the derivative in the clock parameter `beta` at zero. The
derivative is exactly `ell * dvar ell (-1) * primeCoeffSymbol (-3) k ell`. On the
unit circle in `beta`, the clock coefficient is an atom sum with nonnegative
weights and unit-modulus transported atoms. Its norm is bounded by the total
mass. Cauchy's derivative estimate then removes `k` from the upper bound.

The other decomposition proves `Re(z/(1+z)) < 1/2` on the open unit disc and the
corresponding exponential norm bound. This file does not assert an identification
of that exponential's Taylor coefficients with the prime symbol.

The definition `primeCoeffSymbol` was moved unchanged to
`RequestProject/PrimeCoefficientSymbol.lean`. `DraftBPrimeStages.lean` imports that
module; its theorem statements and the arithmetic stage definitions are unchanged.

## Direct compiler verification

Command: `lake env lean RequestProject/PrimeKernelUniformBound.lean`

Exit code: `0`. Literal output:

```text
warning: PrimeNumberTheoremAnd: repository '/Users/samuellavery/work/helix_frobenius/.lake/packages/PrimeNumberTheoremAnd' has local changes
'CriticalLinePhasor.SeatingLedger.Dk_hasDerivAt_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'CriticalLinePhasor.SeatingLedger.clockCoeff_hasDerivAt_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'CriticalLinePhasor.SeatingLedger.primeCoeffSymbol_norm_le_exp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CriticalLinePhasor.SeatingLedger.primeCoeffSymbol_weighted_log_norm_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CriticalLinePhasor.SeatingLedger.cayley_exp_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Log: `/private/tmp/prime-kernel-uniform-final.log`.

SHA256:

```text
18873003e4320447a4fc28b63812c0567ac0e8b02e0b7441ec35aa49cac03773  RequestProject/PrimeCoefficientSymbol.lean
263c20ffd588ab1f08687d0766211001fb6bf84e937bf59555880a3bbf636cf2  RequestProject/PrimeKernelUniformBound.lean
47afdd0bb89fbb624e983ed60475030fb61e712c4d0725b8b3e6a4f711e2f7ec  RequestProject/DraftBPrimeStages.lean
```

## Arithmetic application and build

`RequestProject/DraftBKernelBound.lean` proves

```lean
theorem primeStageKernel_norm_le {n : ℕ} (hn : 2 ≤ n) (k : ℕ) :
    ‖primeStageKernel k n‖ ≤ (n : ℝ) ^ (-1 / 2 : ℝ)

theorem primeStageCoeff_uniform_degree_bound (N k : ℕ) :
    ‖toeplitzCoeff (-3) (primeJetStage anchor20 N) (k + 1)‖ ≤
      ∑ n ∈ Finset.range N,
        ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-1 / 2 : ℝ)
```

The latter bound is independent of degree and depends on the cutoff `N`.
It preserves the actual common anchor phase, with the zero and one terms
handled using the vanishing of the von Mangoldt function there.

Command: `lake build RequestProject.DraftBKernelBound`. Exit code: `0`.
The build includes the changed `DraftBPrimeStages` and its dependent discrepancy module.
Literal final module output:

```text
ℹ [9581/9581] Built RequestProject.DraftBKernelBound (260s)
info: RequestProject/DraftBKernelBound.lean:58:0: 'CriticalLinePhasor.SeatingLedger.primeStageKernel_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RequestProject/DraftBKernelBound.lean:59:0: 'CriticalLinePhasor.SeatingLedger.primeStageCoeff_uniform_degree_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
Build completed successfully (9581 jobs).
```

Full build log: `/private/tmp/draft-b-kernel-build.log`.

Command: `lake env lean RequestProject/DraftBKernelBound.lean`. Exit code: `0`.
Literal output:

```text
warning: PrimeNumberTheoremAnd: repository '/Users/samuellavery/work/helix_frobenius/.lake/packages/PrimeNumberTheoremAnd' has local changes
'CriticalLinePhasor.SeatingLedger.primeStageKernel_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'CriticalLinePhasor.SeatingLedger.primeStageCoeff_uniform_degree_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

Log: `/private/tmp/draft-b-kernel-final.log`.

SHA256:

```text
a5e66a9d34ac822745e31701e1dd591e3313f434c4639b518638c132bf65037b  RequestProject/DraftBKernelBound.lean
```

Source scan:

```text
rg -n 'axiom |sorry|admit|@\[implemented_by\]|exact\?' RequestProject/PrimeCoefficientSymbol.lean RequestProject/PrimeKernelUniformBound.lean RequestProject/DraftBKernelBound.lean RequestProject/DraftBPrimeStages.lean
```

Exit code: `1`, no matches.

## Remaining signed estimate

`DraftBDiscrepancy.lean:304` already supplies a common constant for the gamma term
and the cutoff boundary. The remaining signed expression there is

```lean
primeDiscrepancyStage N k =
  pairedDensityStage (N + 1) k -
    ∑ n ∈ Finset.range N,
      (primeStageKernel k (n + 1) - primeStageKernel k n) *
        (primeMassError (n + 1) : ℂ)
```

No proof of the following estimate has been produced:

```lean
∃ C : ℝ, ∃ p : ℕ, ∀ k, ∀ᶠ N in atTop,
  ‖primeDiscrepancyStage N k‖ ≤ C * (1 + (k : ℝ) ^ p)
```

The scalar bound proved here retains dependence on `n`. It does not provide
this estimate for the signed sum, and no unconditional RH or GRH discharger is
claimed.
