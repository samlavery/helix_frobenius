# Discharge drafts — September 7 update

The current arithmetic route reaches one explicit coefficient sequence at
`s0 = -1+20i`, with `d = -3`. The new `GrowthGap.lean` bounds it by `C*R^k`,
where `R = sqrt(1+3/(1175/2)^2)`. The remaining drafts below target a polynomial
envelope, a family of exponential envelopes approaching base one, or an
arithmetic spectral-trace construction for all Dirichlet characters.

The executable drafts are in
[DischargeDrafts.lean](/Users/samuellavery/work/helix_frobenius/proof-drafts/2026-09-07/DischargeDrafts.lean).
Their signatures remain `RiemannHypothesis` or `GRHSpectral.GRHComplete` with
no added hypotheses. Each ends with a deliberate `fail` at its remaining
construction. These are unfinished proofs, outside the library build glob.
The proved support code is
[ExplicitAnchorDischarge.lean](/Users/samuellavery/work/helix_frobenius/RequestProject/ExplicitAnchorDischarge.lean).
Compiler results and exact axiom outputs are recorded in
[VERIFICATION.md](/Users/samuellavery/work/helix_frobenius/proof-drafts/2026-09-07/VERIFICATION.md).
The support module passed both `lake build` and a direct `lake env lean` check.
The draft check reached exactly the four intended remaining goals, with no
earlier type or import errors. The RH and GRH drafts remain unfinished.

## Evaluation of the recent sources

| Source | What its statement establishes | What to use next |
| --- | --- | --- |
| `HerglotzSweep`, `SeatHerglotzSweep` | Multiplicity-weighted sweep off its poles; inverse Cayley map; exact factor `(1-|z|^2)/|1+z|^2` relating the swept real part to moved seat mass. | Use the identity on its stated domain and retain the normalization. |
| `JetsAreAtoms` | Every explicit jet coefficient equals the corresponding atom coefficient. Positive derivative orders use absolutely convergent zero sums; order zero keeps its finite part. | Supply an estimate for the explicit sequence. |
| `BoundedIffRH`, `SubexponentialAnchor` | Boundedness, polynomial growth, or normalized decay at every `R>1` supplies the zero-location conclusion, with analytic multiplicities retained. | Drafts A–C below. |
| `GrowthGap` | An unconditional **upper bound** `|mu_k| <= C*growthBase^k`; `growthBase < 1+5/1000000`. | Improve the estimate or construct a family of valid bases tending to one. |
| `StripTraceRegularCorrection` | Arithmetic trace correspondence with real spectra and a correction holomorphic through the real spectral axis supplies character-wise GRH. | Draft D below. |

`growthBase` is not proved to equal the actual coefficient growth rate. Thus
its excess above one is an excess in the available majorant, not an exact
measured distance of the sequence from the desired estimate. Its prefactor
`C` is existential; the proof uses the finite total absolute atom weight.
The new support module proves `1 < growthBase` as a separate scalar check.

Ledger 633 incorporates the previous review's clock-sign, cutoff, and
normalization corrections. Its circle-distribution interpretation still
requires constructing a continuous functional on the stated test space;
coefficientwise formulas alone do not supply that continuity. The earlier
finite-prime computations remain measurements at their sampled cutoffs.

## Draft A — direct polynomial estimate

Unfolded target: put
`J(m+1)=(-1)^m/m! * D^m[archSide+primeSide](s0)`, with `J(0)=0`.
Then

`mu_0 = 2*Re J(1)/(-3)` and
`mu_(k+1) = sum_(i=0)^k binom(k,i)*(-3)^(k-i)*(-1)^i*J(k+2-i)`.

Here `primeSide(s)=LSeries Lambda(1-s)` and
`archSide(s)=-weilArch(1-s)`. The next bound is exactly

```lean
∃ C : ℝ, ∃ p : ℕ, ∀ k,
  ‖toeplitzCoeff (-3) (jets explicitLogDeriv ((-1 : ℂ) + 20 * I)) k‖ ≤
    C * (1 + (k : ℝ) ^ p)
```

The first Lean step is
`apply riemannHypothesis_of_explicit_fixed_anchor_polynomial_growth`.
Two decompositions are to estimate the completed coefficient directly, or
to construct a finite-order carrier functional whose evaluation on `w^k`
is this coefficient. In the latter construction, the order and its bound
must be independent of `k`, and the arithmetic identification must be proved.

## Draft B — finite arithmetic stages with a common envelope

This draft has an explicit stage definition rather than an unspecified
approximating family. `primeJetStage s N (m+1)` replaces the prime L-series
in `J(m+1)` by its sum over integers `n < N`. The Archimedean jet is retained
exactly. This differs from the earlier experiment's cutoff on base primes:
here a prime power enters when that integer is below `N`. Every term still
uses the original logarithmic frequency and the same anchor.

The resulting stage is

```lean
toeplitzCoeff (-3)
  (jets archSide anchor20 + primeJetStage anchor20 N) k
```

`explicitCoeffStage_tendsto` proves convergence for each fixed degree to
the actual completed explicit coefficient. Its proof uses absolute
convergence of each logarithm-weighted L-series and the finite jet
dependence of a Toeplitz coefficient. No exchange of two uncontrolled
infinite limits is used.

The remaining bound is

```lean
∃ C : ℝ, ∃ p : ℕ, ∀ k, ∀ᶠ N in atTop,
  ‖explicitCoeffStage N k‖ ≤ C * (1 + (k : ℝ) ^ p)
```

`C` and `p` must be common to every degree. The starting cutoff may depend
on the degree. The proved limit-transfer lemma then supplies Draft A's
bound. The first Lean step is `apply riemannHypothesis_of_explicit_stage_bound`.
Two decompositions are a bound on the combined stage, or a signed remainder
estimate after pairing its prime and Archimedean terms. Separate divergent
uniform terms are not substituted for their completed sum.

This draft asks for a coefficient norm estimate. A negative eigenvalue in
a sampled Toeplitz matrix does not itself disprove such an estimate.

The subsequent [Draft B attempt](/Users/samuellavery/work/helix_frobenius/proof-drafts/2026-09-07/DRAFT_B_ATTEMPT.md)
collects the finite prime terms by integer, computes the end pairing, and tests
the remaining estimates. Its exact source and compiler records are linked there.

## Draft C — bases approaching one

Construct sequences of real numbers `b j` and `C j` satisfying

```lean
(∀ j, 0 ≤ b j) ∧ Tendsto b atTop (𝓝 1) ∧
  (∀ j k, ‖toeplitzCoeff (-3) (jets explicitLogDeriv anchor20) k‖ ≤
    C j * b j ^ k)
```

There is **no requirement that the constants `C j` stay bounded in `j`**.
For a fixed normalization `R>1`, choose one `j` with `b j<R`. The quotient
is bounded by `C j*(b j/R)^k`, which tends to zero. This quantifier order
is proved in `normalized_decay_of_rates_tendsto_one` and consumed by
`riemannHypothesis_of_explicit_rates`.

The first Lean step is the existential `suffices` statement in Draft C.
Two constructions to attempt are arithmetic remainder bounds for a family
of carrier approximations, or a proved unbounded sequence of certified
height bounds feeding the transport estimate. The single height in
`GrowthGap` supplies one rate; the displayed statement requires the full
family and its convergence. No extrapolation of a finite table is made.

## Draft D — GRH from arithmetic spectral traces

For each modulus and character, construct finite real spectra `d n`,
constant counterterms `c n`, and a function `E`. The complete remaining
statement is written in Draft D's executable `suffices` clause. It asks for
local uniform convergence of

`sum_j ((z-d_n(j))^(-1)+c_n(j))`

to `i*(L'/L)(1/2+i*z)-E(z)` off the real axis in the open chart band
`-1/2 < Im z < 1/2`. The correction `E` must be holomorphic on the whole
band, including the real axis. Spectra and counterterms are fixed before
varying `z`. The compiled resonance and holomorphic-limit theorems then
give the zero correspondence.

Two constructions are a sequence of finite self-adjoint pencils with an
identified arithmetic trace, or direct construction of the corrected
arithmetic trace followed by a proved finite-spectrum approximation.
The 3D lifting and carrier-congruence lemmas in `HermitianPencil3D.lean`
preserve the pencil identities. They can supply the operator side; the
trace identification in this draft is the next coupling to construct.

This uses correspondence of singularities, not equality of a zero with an
eigenvector. Analytic multiplicities are retained. For nonreal characters,
the character and its conjugate must be tracked in any reflection step.

## Relation to the older drafts

The earlier growing-bank registration, prime-symbol, theta-stage, and
3D-pencil constructions remain available in the September 5 drafts. Their
remaining estimates are not discharged by `GrowthGap`. The present drafts
place the new explicit coefficient stage and rate-family constructions
next to the existing GRH trace endpoint; they do not alter the unconditional
RH or GRH target signatures.

The [common-bound attempt](COMMON_BOUND_ATTEMPT.md) proves an explicit bound for the
prime symbol uniform in degree, then applies it to the actual arithmetic kernels.
Its finite-sum estimate still depends on the cutoff. Draft B's common polynomial
bound for the end-paired stages remains unproved.

The subsequent [route review and finite section-count proof](ROUTE_REVIEW_AND_SECTION_COUNT.md)
inventories the registered unfinished route families and selects ledger 639's
carrier/anti-carrier section-count construction. Its new Lean modules prove the
exact finite jet-kernel dimension, interpolation and the 3D anti-helix conjugacy
of every Taylor constraint. The arithmetic transport-growth interface is the
next construction on that route.

The [transport closure attempt](TRANSPORT_CLOSURE_ATTEMPT.md) proves exact power
preservation for scalar Cayley transport, computes the linear Taylor-shift
growth of a multiplicity-two section, and proves the purity engine with a
polynomial prefactor. Its two unconditional arithmetic closure attempts reach
the remaining similitude and end-face power bounds; both remain unfinished.
