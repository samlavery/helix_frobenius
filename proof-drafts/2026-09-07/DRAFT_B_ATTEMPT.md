# Draft B — arithmetic estimate attempt

The proof attempts have not closed Draft B. The completed module gives the
exact paired finite sum and an eventual exponential envelope; the common
polynomial estimate remains the last construction in the attempt files.

The target signature stays `RiemannHypothesis`. Its arithmetic goal is

```lean
∃ C : ℝ, ∃ p : ℕ, ∀ k, ∀ᶠ N in atTop,
  ‖explicitCoeffStage N k‖ ≤ C * (1 + (k : ℝ) ^ p)
```

In ordinary quantifiers: choose one real `C` and one natural `p`; for each
degree `k`, choose a cutoff `N_k`; the inequality must hold for every
`N ≥ N_k`. The cutoff can depend on the degree; the envelope cannot.

## Completed arithmetic formulas

[DraftBPrimeStages.lean](/Users/samuellavery/work/helix_frobenius/RequestProject/DraftBPrimeStages.lean)
collects the actual finite prime stages by integer. Write `s=-1+20i` and
`q_k(ℓ)=primeCoeffSymbol (-3) k ℓ`. The definition is the finite polynomial

```text
q_k(ℓ) = Σ_(i=0)^k binom(k,i) (-3)^(k-i) (-1)^i
                    · (-1)^(k+1-i) ℓ^(k+1-i)/(k+1-i)!.
```

The compiled low-degree formulas are `q_0(ℓ)=-ℓ` and
`q_1(ℓ)=ℓ-(3/2)ℓ²`. No signs have been replaced by absolute values.

`pairedPrimeStageCoeff_succ_closed` computes the end pairing exactly:

```text
pairedPrimeStageCoeff N (k+1)
  = (s⁻¹)² · transport(s,0)^k
    + Σ_(n<N) Λ(n)n^(-2) exp(20 i log n) q_k(log n).
```

The phase statement is `anchor_primeTerm_phase`, using the existing
`PrimeClock.phase (-20)`. Its positive exponential sign comes from evaluating
the prime L-series at `1-s=2-20i`. The old `phase_prime_power` theorem keeps
prime powers attached to their base-prime phase.

`explicitCoeffStage_eq_paired` then gives

```text
explicitCoeffStage N k = archRemainderCoeff k + pairedPrimeStageCoeff N k.
```

The end sequence has entries `anchorEndJet m=1/s^m`; its entry at `m=0`
is unused by `toeplitzCoeff`. The separate theorem
`pairedPrimeStageCoeff_zero_closed` retains the original real-part finite
contribution at degree zero.

These identities specify the expression to estimate. They do not assert a
polynomial bound for its norm.

## Earlier normalization and tactic probes

The failed final searches below do not supply a mathematical proof of their
remaining inequalities. They are retained as the record of the earlier run.
The subsequent arithmetic work is in
[DraftBDiscrepancy.lean](/Users/samuellavery/work/helix_frobenius/RequestProject/DraftBDiscrepancy.lean):
summation by parts for the actual von Mangoldt discrepancy, an explicit
Chebyshev estimate, and the cutoff-boundary limit.
The successful direct check and literal axiom outputs are recorded in
[DRAFT_B_DISCREPANCY_VERIFICATION.md](/Users/samuellavery/work/helix_frobenius/proof-drafts/2026-09-07/DRAFT_B_DISCREPANCY_VERIFICATION.md).

1. [DraftBMajorantAttempt.lean](/Users/samuellavery/work/helix_frobenius/proof-drafts/2026-09-07/DraftBMajorantAttempt.lean)
   transfers the existing exponential coefficient bound to the stages and
   tests a constant envelope. The compiler rejects the last comparison
   `C*growthBase^k+1 ≤ 2*(C+1)`.
2. [DraftBConvergenceAttempt.lean](/Users/samuellavery/work/helix_frobenius/proof-drafts/2026-09-07/DraftBConvergenceAttempt.lean)
   uses the exact convergent coefficient to choose a cutoff for each degree.
   Its remaining construction is a single polynomial envelope for
   `‖toeplitzCoeff (-3) (jets explicitLogDeriv anchor20) k‖+1`.
3. [DraftBPairedAttempt.lean](/Users/samuellavery/work/helix_frobenius/proof-drafts/2026-09-07/DraftBPairedAttempt.lean)
   separates degree zero, absorbs its eventual bound into the common
   constant, and expands the positive-degree paired arithmetic expression.
   The final estimate retains the end mode inside the prime sum's norm.
   The corrected check has one error, at the final search on line 44; the
   preceding finite-part transfer and coefficient rewriting elaborated.

The successful stage estimate is

```lean
∃ C : ℝ, ∀ k, ∀ᶠ N in atTop,
  ‖explicitCoeffStage N k‖ ≤ C * growthBase ^ k + 1
```

It is proved as `explicitCoeffStage_eventually_exponential`. Draft B's
polynomial envelope has not been proved by these attempts. The original
draft has not been marked complete or replaced by a conditional signature.

Exact compiler outputs are recorded in
[DRAFT_B_VERIFICATION.md](/Users/samuellavery/work/helix_frobenius/proof-drafts/2026-09-07/DRAFT_B_VERIFICATION.md).
