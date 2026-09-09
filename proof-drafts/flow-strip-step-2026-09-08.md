# Flow strip construction, 2026-09-08

## Fixed object and target

The user identified the flow-warped fiber as
`CriticalLinePhasor.XiKernel.flowStage`; the head-warped alternating bank is the
different object `CarrierHeadFiniteFiber.carrierHeadFiber`.

Unfolded all-positive-warp target:

For every real λ with 0 < λ ≤ 1 and every complex z,
if ∫ u ∈ ℝ, exp(λu²) Kker(u) exp(i z u) du = 0, then Im(z) = 0.

`FlowFrontier λ₀` quantifies this over λ₀ ≤ λ ≤ 1. Both the all-positive-warp
target and `FlowFrontier (1/8)` remain unproved in this patch. No target
signature was replaced by a conditional theorem.

## Construction steps

Expectation-free next action: calculate the effect of an imaginary shift on
one conjugate-root factor and on the actual Fourier integrand.

Two concrete decompositions were executed in Lean:

1. Factor products: the first executable step is
   `simp only [pairFactor, normSq_apply, add_re, add_im, sub_re, sub_im, mul_re,
   mul_im, ofReal_re, ofReal_im, I_re, I_im, pow_two]`, followed by `ring`.
   This proves the exact squared-norm difference for a conjugate pair.
   Induction on a finite product gives its strict norm comparison.
2. Arbitrary real polynomials: the first executable step is
   `have hs := IsAlgClosed.splits (p.map (algebraMap ℝ ℂ))`.
   Factor `p(z) * conj(p(conj(z))) = p(z)^2` using the full algebraic-root
   multiset. This avoids choosing conjugate-pair representatives and retains
   every multiplicity. It extends the comparison to all nonzero real
   polynomials, including the constant case.

The resulting `polynomial_shift_zero_strip` proves that a zero of
`p(z+ih)+p(z-ih)` satisfies
`Im(z) = 0 ∨ Im(z)^2 + h^2 ≤ Δ^2`, when all roots of p have squared imaginary
part at most Δ² and h > 0. It does not assume simple roots or real-rootedness.

For the actual flow, `flowStage_symmetric_shift` proves the exact cosh
multiplier identity. The approximants are explicitly

`coshStep λ n z = ∫ cosh(sqrt(2λ/(n+1)) u)^(n+1) Kker(u) exp(i z u) du`.

`tendstoLocallyUniformly_coshStep` proves their locally uniform convergence
to `flowStage λ` for 0 ≤ λ ≤ 1. The proof sandwiches the multipliers between
`(1 + λu²/(n+1))^(n+1)` and `exp(λu²)`, and applies dominated convergence
with the existing `Kker_bound` and `integrable_Dq` estimates.

There is no real-rootedness theorem for these approximants in this patch.

## Searches performed

Representative literal commands (repo root):

```sh
rg -n 'deBruijn|de_bruijn|stripNarrow|strip_narrow|realRooted|real_rooted|FlowFrontier|flowFrontier' RequestProject .lake/packages/mathlib/Mathlib
rg -n 'flowStage|flow_stage|heatEquation|heat_equation|root_velocity|zeroVelocity|collision|Collision' RequestProject
rg -n 'conjugatePair|conjugate_pair|pairedFactor|pair_factor|strip_shrink|stripShrink|cosh.*zero|zero.*cosh' RequestProject .lake/packages/mathlib/Mathlib
rg -n 'prod.*roots|eval.*prod|prod.*eval|map.*conj' .lake/packages/mathlib/Mathlib/Algebra/Polynomial/Roots.lean .lake/packages/mathlib/Mathlib/Analysis/Complex/Polynomial/Basic.lean .lake/packages/mathlib/Mathlib/Algebra/Polynomial/Splits.lean
rg -n 'TendstoLocallyUniformly.*Polynomial|Polynomial.*TendstoLocallyUniformly|exists.*polynomial.*[Ss]trip|polynomialApprox|polynomial_approx|xi.*approx' RequestProject .lake/packages/mathlib/Mathlib/Analysis
rg -n 'cosh.*(nhds|IsLittleO|isLittleO)|sinh.*div.*(zero|nhds)|tendsto.*pow.*exp|pow.*tendsto.*exp' .lake/packages/mathlib/Mathlib/Analysis
```

LeanSearch queries included real-entire Fourier heat strip narrowing;
polynomial factorization with roots and multiplicities; and limits of powers
approaching the exponential. Loogle queries included `"roots", "derivative"`
and `"tendsto", "pow", "exp"`. A first Loogle query with missing comma failed
and was corrected. Relevant discoveries used in the code include
`Polynomial.Splits.aeval_eq_prod_aroots`, `Polynomial.aeval_conj`,
`Real.cosh_le_exp_half_sq`, and `Real.tendsto_one_add_div_pow_exp`.

`FlowFrontier.lean` was checked with `lake env lean`; its two printed
declarations have only `[propext, Classical.choice, Quot.sound]`. Its frontier
theorem consumes a frontier proof; it does not supply one.

## Next concrete construction

Extend the polynomial shift theorem to the xi-section using real polynomial
approximants whose zeros remain in the initial strip. Candidate statement:

```lean
theorem xiSection_polynomial_strip_approx :
    ∃ P : ℕ → Polynomial ℝ,
      TendstoLocallyUniformly (fun (n : ℕ) (z : ℂ) => (P n).aeval z)
        CriticalLinePhasor.XiChannel.xiSection atTop ∧
      ∀ n, P n ≠ 0 ∧ ∀ z : ℂ, (P n).aeval z = 0 → z.im ^ 2 ≤ (1 / 2 : ℝ) ^ 2
```

This candidate is a next proof obligation, not a compiled result.

The relevant existing factorization is
`ZD.riemannXi_hadamard_factorization` in `XiHadamardFactorization.lean:378`.
It was located and read, but its axiom footprint was not independently
audited during this patch, and it is not imported by the new files.
