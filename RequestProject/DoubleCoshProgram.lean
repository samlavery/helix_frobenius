import RequestProject.DoubleCoshRiemannBridge
import RequestProject.RiemannHypothesisBridge

/-!
# Double-Cosh Program — Top-Level Integration

This file integrates the full double-cosh chain, from pair algebra through
Riemann's integral bridge to Mathlib's `RiemannHypothesis`. It exposes the
unconditional infrastructure as named theorems and states the single
remaining open content — **no-offline** — as a clean hypothesis that, when
proved (by any route, including the parallel `no_offline` proof effort),
closes `RiemannHypothesis`.

## The chain

```
                   [no-offline]                 (open, target)
                        |
                        ↓
 ∀ ρ ∈ NontrivialZeros, ρ.re = 1/2              (our internal RH form)
                        |
                        ↓  no_offline_zeros_implies_rh  (unconditional)
                        |
                 RiemannHypothesis              (Mathlib, def)
```

and dually, via the classifier:

```
 R_double(ρ.re, r) = 0 on NontrivialZeros       (classifier balance)
                        ↕  classifier_iff_online  (unconditional biconditional)
 ∀ ρ ∈ NontrivialZeros, ρ.re = 1/2
```

## Infrastructure files

1. **`DoubleCoshResidue`** — classifier factorization:
   `R_double(β, r) = 4·sinh²((β−1/2)·log r)·sinh²((1/2−π/6)·log r)`
2. **`DoubleCoshValidation`** — soundness/completeness against
   `riemannZeta`'s nontrivial zeros. Bidirectional reformulation of RH.
3. **`CoshZetaIntertwiner`** — Klein-180 intertwiner with FE + conjugation.
4. **`RiemannHypothesisBridge`** — bridges our internal `∀ ρ, ρ.re = 1/2`
   to Mathlib's `RiemannHypothesis` predicate.
5. **`DoubleCoshExtension`** — Stage A: complex pair kernel, FE pair
   relation, Schwarz lifts, ψ decomposition.
6. **`DoubleCoshStageB`** — Stage B proved: `finitePairedIntegral_of_odd_vanishes`
   (paired integral annihilates odd ψ).
7. **`DoubleCoshStageC`** — Stage C structural: real-ψ factored form,
   target stated.
8. **`DoubleCoshKernelComparison`** — per-kernel and pair-sum/difference/
   product decompositions; FE-even/odd structure.
9. **`DoubleCoshRiemannBridge`** — the near-collinearity pointer: any
   `cosh((s−1/2)·t)` integral rewrites as paired-cosh integral.

## What's unconditional (no sorry, no custom axioms)

All 9 files above build with axiom footprint `[propext, Classical.choice, Quot.sound]` only.
Specific capstones:

* `classifier_iff_online`: `pairAgreementDefect r ρ.re = 0 ↔ ρ.re = 1/2`
  for `r > 1` on nontrivial zeros.
* `rho_online_iff_residue_zero`: `ρ ∈ OnLineZeros ↔ pairAgreementDefect r ρ.re = 0`.
* `no_offline_zeros_implies_rh`: `(∀ ρ ∈ NontrivialZeros, ρ.re = 1/2) → RiemannHypothesis`.
* `classifier_balance_implies_RiemannHypothesis`: classifier balance at one scale `r > 1` gives `RiemannHypothesis`.
* `finitePairedIntegral_of_odd_vanishes`: Stage B Condition (3).
* `cosh_shift_half_via_pair`: algebraic inversion for Riemann-style bridge.

## What closes the chain

Any proof of

```
∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros → ρ.re = 1/2
```

-- via any route (classifier, Riemann bridge, independent no-offline
analysis, parallel GPT proof effort) -- closes `RiemannHypothesis` via
`no_offline_zeros_implies_rh`.
-/

open Complex ZetaDefs DoubleCoshResidue DoubleCoshValidation RHBridge

noncomputable section

namespace DoubleCoshProgram

/-! ### §1. The no-offline hypothesis and its consequence -/

/-- **The open target**: no nontrivial zero is offline. Named hypothesis
so parallel proof efforts can plug in. -/
def NoOfflineZeros : Prop :=
  ∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros → ρ.re = 1/2

/-- **Capstone**: `NoOfflineZeros` closes `RiemannHypothesis` unconditionally. -/
theorem RiemannHypothesis_of_no_offline (h : NoOfflineZeros) : RiemannHypothesis :=
  no_offline_zeros_implies_rh h

/-! ### §2. Classifier door — pair-agreement balance gives the internal form -/

/-- **Universal classifier-balance at any single admissible scale gives `NoOfflineZeros`**. -/
theorem noOfflineZeros_of_classifier_balance {r : ℝ} (hr : 1 < r)
    (h : ∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros → pairAgreementDefect r ρ.re = 0) :
    NoOfflineZeros := by
  intro ρ hρ
  exact (classifier_iff_online ρ hρ hr).mp (h ρ hρ)

/-! ### §3. Consumer interface — a single theorem any `no_offline` proof can
hit -/

/-- **The single theorem any proof route should target**: `NoOfflineZeros`.
If you can prove it, this file + `RiemannHypothesisBridge` gives you
`RiemannHypothesis`, no additional work needed.

Parallel proof efforts (GPT working on no-offline, classical analytic
approaches, the paired-cosh bridge when Riemann's ξ-integral is
formalized) all land here. -/
theorem target_theorem : NoOfflineZeros → RiemannHypothesis :=
  RiemannHypothesis_of_no_offline

/-! ### §4. Axiom hygiene -/

#print axioms noOfflineZeros_of_classifier_balance
#print axioms target_theorem

end DoubleCoshProgram

end
