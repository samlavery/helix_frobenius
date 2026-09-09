# Route review and the finite section-count proof

Inventory basis: the live route families indexed by `HP_SKELETON.md`, the updated
mainline in `C3_SKELETON.md`, ledgers 638–639, the September 5 drafts in
`RH_DISCHARGE_DRAFTS.md`, and the September 7 executable drafts. Historical
variants that feed the same remaining input are grouped in one row.

## Remaining inputs, by route

| Route | Source and remaining construction |
| --- | --- |
| Explicit coefficient growth; September 7 A | [SubexponentialAnchor.lean:225](/Users/samuellavery/work/helix_frobenius/RequestProject/SubexponentialAnchor.lean:225): bound the completed coefficients at `anchor20`, uniformly in degree. `GrowthGap` supplies one exponential upper bound; its base is not an equality for the actual growth rate. |
| Common finite-stage bound; September 7 B | [ExplicitAnchorDischarge.lean:81](/Users/samuellavery/work/helix_frobenius/RequestProject/ExplicitAnchorDischarge.lean:81): construct common `C,p` with `∀ k, ∀ᶠ N, ‖explicitCoeffStage N k‖ ≤ C*(1+k^p)`. [DraftBDiscrepancy.lean:304](/Users/samuellavery/work/helix_frobenius/RequestProject/DraftBDiscrepancy.lean:304) removes the bounded archimedean term and the fixed-degree boundary. The remaining signed discrepancy needs a common degree envelope. `DraftBKernelBound` is uniform in degree but its finite-sum majorant still depends on cutoff. |
| Rate family; September 7 C | [ExplicitAnchorDischarge.lean:109](/Users/samuellavery/work/helix_frobenius/RequestProject/ExplicitAnchorDischarge.lean:109): construct `b j → 1` and estimates `‖μ k‖ ≤ C j * b j ^ k` for every `j,k`. The constants may vary with `j`. |
| Full prime quadratic form; Track S and earlier B | [XiJetsArithmetic.lean:164](/Users/samuellavery/work/helix_frobenius/RequestProject/XiJetsArithmetic.lean:164), [PrimeSymbolClock.lean:376](/Users/samuellavery/work/helix_frobenius/RequestProject/PrimeSymbolClock.lean:376): prove the sign of the completed DC plus phase sum for every polynomial and anchor. Pascal reduction and the explicit prime symbol are available. A symbol minor does not determine the sign of the completed arithmetic form. Prime powers retain their base-prime phase relation; the order-zero finite part remains in the completed pairing. |
| Fixed self-adjoint receiver; HP | [CaptureInterfaceAudit.lean:193](/Users/samuellavery/work/helix_frobenius/RequestProject/CaptureInterfaceAudit.lean:193): construct the operator and the completed arithmetic trace identification with regularity off its spectrum. This consumer is for nonprincipal characters; a complete character family also handles the principal case. |
| Unitary Cayley receiver / two-point trace | [SeatingLensCayley.lean:77](/Users/samuellavery/work/helix_frobenius/RequestProject/SeatingLensCayley.lean:77): exhibit the unitary element, continuous readout and the stated arithmetic resolvent-difference identity on the lens. The identity must hold for the same fixed receiver as the spectral parameter varies. |
| Finite real spectral towers; September 7 and earlier D | [StripTraceRegularCorrection.lean:47](/Users/samuellavery/work/helix_frobenius/RequestProject/StripTraceRegularCorrection.lean:47): construct real spectra, fixed counterterms, a correction holomorphic on the whole spectral strip, and the stated locally uniform arithmetic trace limit. |
| 3D Hermitian pencil limit | [HermitianPencil3D.lean:148](/Users/samuellavery/work/helix_frobenius/RequestProject/HermitianPencil3D.lean:148): couple arithmetic vanishings to states with positive limiting metric mass and vanishing imaginary part of the **full** pencil pairing. Spatial lifting and Hermitian congruence already preserve the operator facts. |
| Height intertwining / Green transport | [HelixHeightDischarge.lean:100](/Users/samuellavery/work/helix_frobenius/RequestProject/HelixHeightDischarge.lean:100): prove the particular kernel descent, Green transport, or zero-ledger symmetry consumed by the three semiconjugacy dischargers. The geometric carrier symmetry alone supplies neither of those arithmetic identifications. |
| Registration, `S(t)` warp, growing-bank census; earlier A / Track C | [RegistrationCalibration.lean:116](/Users/samuellavery/work/helix_frobenius/RequestProject/RegistrationCalibration.lean:116), [HelixHubFusion.lean:41](/Users/samuellavery/work/helix_frobenius/RequestProject/HelixHubFusion.lean:41): control the integrated full-census defect sublinearly, retaining native, boundary and bank-change terms and analytic multiplicities. Integer boundary calibration is available. |
| Explicit theta stages / escort law; earlier C and C3 M1-F | [XiStageMass.lean:38](/Users/samuellavery/work/helix_frobenius/RequestProject/XiStageMass.lean:38), [SeatingStageDoor.lean:80](/Users/samuellavery/work/helix_frobenius/RequestProject/SeatingStageDoor.lean:80): prove eventual stage-mass sign for the actual `xiArithmeticStage` on the required channel. The factor-two integral identification, stage holomorphy, and convergence of values and derivatives are completed inputs, not remaining approximation tasks. |
| Source-labelled cascade; Track N | [SourceLabelledCascade.lean:63](/Users/samuellavery/work/helix_frobenius/RequestProject/SourceLabelledCascade.lean:63): construct an entire convergent cascade with the stated source-labelling property at every stage. The two-phasor example later in that file tests why phasor provenance by itself does not supply that property. |
| Weil support ladder and Suzuki/trace readout; Tracks W/E | [HP_SKELETON.md:954](/Users/samuellavery/work/helix_frobenius/HP_SKELETON.md:954): the smooth explicit formula, cubic/linear taper identities and END residues are available. The supply step is positivity at unbounded support or an identified positive receiver. The Suzuki route additionally calls for the actual arithmetic Gram/isometry identification; a finite-range Gram computation is an instrument. The fully sharp cutoff and digamma residue-sum expansion are additional unfinished analytic normalizations recorded in Track W. |
| Frobenius duality, cup growth, carrier × anti-carrier surface; ledger 639 **selected** | [WeilDuality.lean:223](/Users/samuellavery/work/helix_frobenius/RequestProject/WeilDuality.lean:223): supply the two transport-growth inequalities for identified nonzero vanishing classes. `ChiralCup` supplies a positive Gram space. `NeronSeveriRung` supplies a formal rank-three lattice with faithful pairing readout. The first new construction below is the finite Cayley-bank section count. The surface intersection/effectivity bridge to arithmetic flow classes remains to be built. |
| Carrier-native orbital lift / Maass-CPS / Langlands | [CPSRemainingObligationsAudit3D.lean:23](/Users/samuellavery/work/helix_frobenius/RequestProject/CPSRemainingObligationsAudit3D.lean:23): construct a cuspidal automorphic realization and its Hecke/Satake compatibility, beyond coefficient identities. The divisor sequence satisfies the present coefficient interface while its first symmetric-power prime average is two. The scalar adelic action also requires compatibility with its separately stored Satake data. Ledger 638's rank-two orbital-data lift is a further construction target. Mellin convergence results in `CPSMellinFEDischarge` retain their stated kernel/duality inputs. |
| Simplicity and Newman-flow barrier | [HP_SKELETON.md:1249](/Users/samuellavery/work/helix_frobenius/HP_SKELETON.md:1249): prove nonvanishing of the arithmetic derivative at crossings, or the registered pairwise flow barrier and its bank transport. The de Bruijn–Newman flow infrastructure is also a listed construction task. Simple geometric events do not erase multiplicity in the analytic census. |

Track A's analytic approximation package is completed in the updated skeleton.
The new `GammaJetsSeries.lean` also provides positive-order polygamma series;
the older Track W statement that the needed gamma-series infrastructure is
entirely absent is outdated. Its remaining contour/residue-sum assembly must use
those new results with the zero-order normalization retained.
Tracks B and D remain measurement/falsification registers. Track P is marked retired
by the user in the skeleton. These statuses do not add unfinished proof targets to
the table.

## Selected construction, unfolded

Let `a : ι → K` be an injective finite configuration in a field, let `m i` be its
prescribed multiplicities, and let `M = ∑ i, m i`. The bank is the vector space
of polynomials of degree less than `N`. Its actual jet map is

```text
E(P)(i,j) = coefficient_j(P(a_i + X)),       0 ≤ j < m_i.
D(X)     = ∏ i (X-a_i)^(m_i).
```

[FiniteCellSections.lean](/Users/samuellavery/work/helix_frobenius/RequestProject/FiniteCellSections.lean)
constructs multiplication by `D` as a linear equivalence from the `N-M` mode
bank to the section space. Coprimality at distinct nodes identifies that space
with the kernel of `E`. The proved statements are:

```text
dim ker E = N - M                         (natural, truncated subtraction)
dim range E = min N M
M ≤ N  ⇒  E is surjective
N ≤ M  ⇒  every vanishing section is zero
a nonzero vanishing section exists  ↔  M < N
```

The existence direction exhibits `D` itself. These results include the empty
configuration, zero multiplicities and zero modes. Injectivity is essential to
the independent-jet interpretation: repeated nodes are not silently treated as
distinct constraints. No analytic zero set or arithmetic function is used.

The two decompositions were executed in Lean:

1. `multiplyInto` / `sectionEquiv`: division by the explicit monic divisor and
   exact degree arithmetic.
2. `jetEvaluation` / `jetKernelEquiv`: the simultaneous linear evaluation map,
   its actual kernel, then rank-nullity and interpolation.

## 3D attachment and anti-helix

[HelixCellSections3D.lean](/Users/samuellavery/work/helix_frobenius/RequestProject/HelixCellSections3D.lean)
uses the existing `ConeProjection.Fiber` and `GlobalHelix.globalHelixInvolution`.
For a fiber `(r,θ,h)`, its node is the existing retained-height Cayley readout
`(h-i)/(h+i)`. Every node has norm one. Distinct retained heights give distinct
nodes, and the finite section count and interpolation theorem apply.

The bank here consists of **consecutive powers of this Cayley coordinate**.
It is not yet identified with a finite prime-frequency bank or with all sections
on a carrier-product surface. Radius and phase remain in the existing loss
ledger; projection is not asserted injective on the entire three-dimensional
space.

For `J(r,θ,h) = (r,-θ,-h)`, the proof transports **each Taylor coefficient**:

```text
jet_j(conjugate-coefficient P, circleReadout(J f))
    = conjugate(jet_j(P, circleReadout f)).
```

Consequently vanishing at every prescribed order and the kernel dimension are
preserved by the anti-helix involution. This is the existing geometric
conjugacy applied to the actual section constraints.

## Next construction on this route

The finite section-count node is proved. The next interface is a support-indexed
space of sections for the arithmetic flow classes, with a proved pairing law
that turns effective section data into the growth input of
[WeilDuality.lean:231](/Users/samuellavery/work/helix_frobenius/RequestProject/WeilDuality.lean:231):

```lean
∀ k : ℕ, ‖(T ^ k) v‖ ^ 2 ≤ Cα * B ^ k * ‖v‖ ^ 2
```

The companion strand requires the corresponding statement for `w`.
No such transport bound is claimed by the finite polynomial dimension theorem.
The RH and GRH target declarations and the four executable unfinished drafts
are unchanged.

## Search and dependency audit

The searches used `rg` over `RequestProject` and the local Mathlib sources.
The construction searches included:

```sh
rg -n 'section.*count|finrank.*vanish|vanishing.*space|Riemann.*Roch' RequestProject
rg -n 'degreeLT|divMod.*Equiv|finrank_range_of_inj|X_sub_C_pow_dvd|X_pow_dvd_iff|pairwise_coprime_X_sub_C|prod_dvd_of_coprime|natDegree_prod_of_monic' .lake/packages/mathlib/Mathlib
rg -n 'finrank_range_add_finrank_ker|surjective_of_finrank|finrank_eq.*top|taylor.*smul|finrank_pi|finrank.*pi' .lake/packages/mathlib/Mathlib/LinearAlgebra .lake/packages/mathlib/Mathlib/Algebra/Polynomial/Taylor.lean
rg -n 'cayley.*inject|inject.*cayley|cayley.*eq.*iff|cayley.*inv' RequestProject .lake/packages/mathlib/Mathlib
rg -n 'taylor.*map|map.*taylor|taylor.*comp|coeff_map|map.*X_sub_C|conj.*Polynomial' .lake/packages/mathlib/Mathlib/Algebra/Polynomial
rg -n 'rh_iff_prime_jets_nonneg|primeJetsForm_eq_dc_add_phase|grh_of_selfAdjoint_completed_resolvent_capture|riemannHypothesis_of_stage_mass' RequestProject
```

LeanSearch queried degree-bounded polynomial spaces, vanishing Taylor
coefficients, and compatibility of Taylor expansion with coefficient maps.
Loogle queried `Polynomial.degreeLT, Module.finrank`,
`"finrank", "range", "injective"`, and `Polynomial.taylor, Polynomial.map`.

The existing theorem consumers and geometric prerequisites are checked in
[RouteAxiomAudit.lean](/Users/samuellavery/work/helix_frobenius/proof-drafts/2026-09-07/RouteAxiomAudit.lean).
Their axiom footprints audit their proof bodies; the outstanding parameters in
their statements are the inputs recorded above. The new proof endpoints print
their own axiom dependencies in their source files.

Exact compiler output and source hashes are recorded in
[SECTION_COUNT_VERIFICATION.md](/Users/samuellavery/work/helix_frobenius/proof-drafts/2026-09-07/SECTION_COUNT_VERIFICATION.md).
