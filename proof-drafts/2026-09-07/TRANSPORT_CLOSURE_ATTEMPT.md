# Transport closure attempt

The target remains the unconditional `RiemannHypothesis` declaration. This turn
constructs and checks the operator step following the finite section count.

## The concrete operators

[HelixSectionTransport.lean](/Users/samuellavery/work/helix_frobenius/RequestProject/HelixSectionTransport.lean)
proves two separate statements about specified transports.

For a 3D fiber `f`, scalar multiplication by `circleReadout f` preserves the
norm at every power. This has the exact bound `C = B = 1`, on any complex normed
space. Its DC, power zero, is the identity.

For multiplication by `X` on two Taylor coefficients, the actual operator is

```text
T_a(u,v) = (a*u, u+a*v).
```

`twoJetTransport_taylor` identifies this with the Taylor coefficients of `X*P`.
At carrier height zero the Cayley node is `a = -1`, and the exact iterate is

```text
T_(-1)^k(1,0) = ((-1)^k, -k*(-1)^k).
```

The second-coordinate norm is exactly `k`. Therefore this particular orbit has
no constant norm envelope. Its proved squared-norm envelope is `2*(1+k^2)`.
The norm here is the standard product maximum norm on `ℂ × ℂ`.

The vector `(1,0)` is a generalized eigenvector. The original
`WeilDuality.purity_from_castelnuovo` theorem, whose vectors are eigenvectors,
is unchanged. This calculation tests an attempted bound on the entire jet
space and retains the off-diagonal Taylor contribution.

## Polynomial-prefactor purity

[WeilPolynomialGrowth.lean](/Users/samuellavery/work/helix_frobenius/RequestProject/WeilPolynomialGrowth.lean)
proves the following argument and composes it with the existing duality engine:

```text
B > 0 and |alpha|^(2k) <= C*(1+k^p)*B^k for every k
    imply |alpha|^2 <= B.
```

If `|alpha|^2 > B`, divide the bound by `|alpha|^(2k)`. Its left side becomes
one. The right side tends to zero: it is a fixed polynomial times powers of a
ratio strictly between zero and one. The contradiction is implemented using
Mathlib's geometric-decay theorem. No positivity assumption on `C` is inserted.

`cup_polynomial_growth_gives_purity` applies this to a nonzero eigenvector of
the actual specified transport. `purity_from_polynomial_castelnuovo` uses
`alpha*beta = B` and both strands' bounds to obtain both norms equal to `sqrt B`.
The two polynomial degrees and constants may differ.

## Arithmetic closure checks

[TransportClosureAttempts.lean](/Users/samuellavery/work/helix_frobenius/proof-drafts/2026-09-07/TransportClosureAttempts.lean)
keeps two literal `example : RiemannHypothesis` targets. It is an executable
draft outside the library build glob.

Attempt A uses a section-count weight: one node, multiplicity one, and two
available modes. The computed weight is one at every parameter; its positivity
and reflection invariance are proved. The next check is its arithmetic
similitude law at nontrivial zeros.

Attempt B uses the exact 3D phase-transport power theorem. It discharges the
verified-height case with `endPairFace_two_sided_power_bounds_below_1269o2`,
then tests the identification of the geometric norm envelope with the two
arithmetic end-face envelopes above that height.

The source search also traced `HelixPolarization.theoremD` to the quotient
`ℂ / span{L(ρ)}` and its class of one. That theorem supplies a nonzero quotient
class at a vanishing. The local similitude operator `frobT` is separately
defined in the same module; using it on that class still calls for an action
and the arithmetic eigenvalue identification.

## Verification

Both new library files pass direct Lean checks and the targeted build.
The arithmetic draft returns exit code 1. Attempt A reaches
`Real.exp (ρ.re - 1 / 2) ^ 2 = 1`. Attempt B reaches the two bounds
`‖endPairFace ρ‖ ^ (2*k) ≤ 1` and its reflected companion. Neither unconditional
RH example is complete.

Direct compiler output, the targeted build, axiom audits, and the arithmetic
draft's actual proof states are recorded in
[TRANSPORT_CLOSURE_VERIFICATION.md](/Users/samuellavery/work/helix_frobenius/proof-drafts/2026-09-07/TRANSPORT_CLOSURE_VERIFICATION.md).

## Search record

```sh
rg -n 'castelnuovo|Castelnuovo|cup_growth|cupGrowth|hcupα|hgrowα|transport.*(norm|bound)|norm.*transport|powerBound|power_bound|half.unit.*growth' RequestProject .lake/packages/mathlib/Mathlib
rg -n 'polynomial.*purity|purity.*polynomial|polynomial.*cup|cup.*polynomial' RequestProject .lake/packages/mathlib/Mathlib
rg -n 'HasEigenvector.*pow|HasEigenvalue.*pow|pow_apply.*eigen|apply_pow.*eigen|mem_eigenspace.*pow|eigen.*pow_apply|pow_apply_eq' .lake/packages/mathlib/Mathlib/LinearAlgebra/Eigenspace
rg -n 'Jordan.*pow|jordan.*pow|pow.*Jordan|mul_X.*taylor|taylor_mul|coeff_mul_X|coeff_X_mul|pow.*binom|tendsto.*pow.*mul.*zero' .lake/packages/mathlib/Mathlib
rg -n 'section.*transport|transport.*section|transport.*Jet|[Jj]et.*transport|finrank.*grow|dimension.*grow' RequestProject
rg -n 'theoremD|theoremB|theoremA|primitive|vanishing|class' RequestProject/HelixPolarization.lean
```

LeanSearch queried polynomial times geometric decay. Loogle queried
`Filter.Tendsto, "pow", "mul", "zero"`. The actual `HasEigenvector.pow_apply`
and order-limit signatures were then read from Mathlib source.
