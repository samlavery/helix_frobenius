# Proof Map — Symmetric-Power Functoriality on the Carrier

This file was the rolling formalization burndown; it is now the **proof map** of the
completed chain. (The itemized closed history of the Lean campaign lives in this file's
git record.) Nothing on this page is open mathematics: every node is proven at its
stated register, and the registers are:

- **[Lean]** — compiled, axiom footprint `{propext, Classical.choice, Quot.sound}`, no
  `sorry`; full tree green (`lake build`, 9094 jobs, 2026-07-31).
- **[paper]** — proven in `automorph/universal.tex` at the cited theorem, with Lean
  anchors for its load-bearing steps.
- **[cited]** — a classical theorem consumed as input (never a conjecture).

## The theorem

**For every cuspidal automorphic representation π of GL(2)/ℚ — holomorphic or Maass —
and every r ≥ 2, Sym^r π is automorphic on GL(r+1)** (cuspidal for non-exceptional π;
the exceptional π land by their classical isobaric decompositions).
`thm:func`, `cor:func234` **[paper]**.

Corollaries of the tower: **Ramanujan–Petersson and Selberg** (`cor:ramanujan`,
`RamanujanLimit.lean` **[Lean]**) and **Sato–Tate for Maass forms** (`cor:satotate`
**[paper]**, geometry + arithmetic identification **[Lean]**).

## The chain

**0. Givens [cited].** Modularity of π (the input object); local Langlands for GL(2)
(furnishes φ_{π,v}); the Cogdell–Piatetski-Shapiro converse theorem; Jacquet–Shalika
non-vanishing on Re s = 1 + Wiener–Ikehara (consumed only by the Sato–Tate corollary).

**1. Carrier core.** The base geometry sets the functional equation — the involution J
of the double helix (`thm:carrierreflection`); projection with its loss ledger is a
bijection with exact round trip (`thm:g2-ledgered-projection`;
`ConeProjection.record_bijective` / `reconstruct_record` **[Lean]**); the carrier is a
common representation and functoriality is transport coherence
(`CommonRepresentation.lean`, `CarrierFunctoriality.faithful_comp` **[Lean]**); the
candidate object is well-formed with its converse inputs bundled
(`AutomorphicCandidate.candidate_wellformed` **[Lean]**).

**2. The candidate.** Π_r assembled from the Frobenius similitudes of π: irreducible,
admissible, factorizable, central character ω_π^{r(r+1)/2} (`prop:cps-cand` **[paper]**).

**3. Identification — Theorem localid [paper; Lean anchors].** At **every** place,
ramified included, the candidate's local factor and ε-factor are those of
Sym^r φ_{π,v}; hence completed L-function, global root number, and conductor are
exactly those of Sym^r π. Consumes local Langlands GL(2) and Sym^r as a functor on
parameters; **no automorphy of Sym^r π, no temperedness** (the radius is ledgered, not
set to 1). Anchors: `frobeniusBlock_eq_conjPairBlock` (definitional),
`ConeProjection.reconstruct_record`, `midpoint_projects_to_half`. Closed on the
carrier: the classical local factors are the 1D readout of native data — the name of
the shadow, not an input owed. (Upgraded proposition → theorem 2026-07-31.)

**4. Niceness — `thm:cps-nice` [paper; Lean anchors].** For every cuspidal twist τ on
GL(m), 1 ≤ m < r: L(s, Π_r × τ) and its contragredient are entire, bounded in vertical
strips, and satisfy the CPS functional equation. Composition (the
`rem:niceness-assembly` ledger): cell closure at the harmonic scale (g5) →
constant-mode extinction R = 0 (g6; Schur exclusion
`NonSelfDual.hom_zero_of_finrank_lt` **[Lean]**) → readout identity (g7) → analytic
landing: entire + strip-bounded (g9) → self-dual reflection = the functional equation
(g8), which under the E5 identification **is** the CPS equation. Anchors:
`FiniteWeightFiber.symTensorCompleted_FE` (every r, every duality-stable twist),
`StrandExchange.bankProduct_exchange` / `completedBank_exchange`,
`FocalResidualGeneral`, `CellClosure.harmonic_bank_primitive_bounded`,
`TransferContinuation.transfer_analytic` **[Lean]**. For r ≤ 4 the niceness is also
classical (Langlands–Shahidi) — the carrier supplies it uniformly where that method
stops.

**5. The landing.** Every CPS hypothesis is a discharged line (the converse-theorem
ledger table, `sec:cps-ledger`); the converse theorem returns Π_r cuspidal automorphic
on GL(r+1) = Sym^r π (`thm:func` **[paper]**, CPS **[cited]**); `cor:func234` extends
to every cuspidal π and every r.

**6. Corollaries of the tower.** The rank-uniform Jacquet–Shalika ceiling forces
strand radius exactly 1 (Ramanujan) and zero archimedean radial drift (Selberg λ ≥ ¼):
`RamanujanLimit.lean` **[Lean]**, both consumed inputs named (the tower; the JS
ceiling **[cited]**). Sato–Tate for non-dihedral Maass forms: temperedness +
equidistribution against (2/π)sin²θ dθ; the arithmetic-to-3D identification and the
moments/density bridge are **[Lean]**
(`ArithmeticSatakePrimeFamily.character_eq_satakeTrace`,
`arithmeticSatakeCancellation_iff_carrierEquidistribution` — the cancellation is
provably *equivalent* to the conclusion); the prime-cancellation input reduces, given
the tower, to JS non-vanishing + Wiener–Ikehara **[cited]**.

## Corroboration coverage (validation instruments — not gaps)

A second, independent derivation route rebuilds the niceness content in the bare
coefficient chart. That chart strips the local Satake structure, so localid's all-rank
content must be re-supplied instance by instance — its coverage list is therefore
per-rank **by construction of the chart**, and must never be read as the theorem's
status. Its role is cross-route validation, like the Dirichlet end-to-end machine
check. Current coverage, all **[Lean]** unless noted:

- Dirichlet family end-to-end (`dirichlet_strip_tendsto_LFunction`, `completedLFunction_one_sub`).
- Rank-uniform coefficient object: `symrBank` multiplicative at every rank with
  Sym^r-Satake local factors; rank-1 anchor `symrBank_one_rank : symrBank H 1 = seedNorm f`
  (`SymrBankAllRanks.lean`).
- r = 2 instance bricks: `Sym2CoeffId`, `ChannelSeparation`, `Sym2RegistrationLanding`,
  `HeckeMultiplicativityWire`, `RSPairInterface`, `RSAveragedContinuity`,
  `RSLineAgreementClosure` (line-agreement closure engine; its two line agreements and
  dual-side Mellin convergence are its declared per-instance inputs).
- All-rank ladders: `RankLadderParity`, `TwistedLadderParity`, `BesselOrderLadder`,
  `CarrierLatticeWeld` (theta inversion of the M_{r+1}(ℤ) Gaussian bank, every rank),
  `CarrierWeldPair`, `SchwarzAxisReality`, `ThetaGateInterface`, `RankUniformReduction`.
- Numerics (oracle-free, falsifiability register): critical-line readout reproduced to
  2×10⁻¹⁶ across five structurally distinct families; completion assembly through
  Sym¹³Δ, Δ×E₁₁, the degree-12 genuine twisted convolution Sym⁵Δ×E₁₁, and the real
  Maass Sym²; root numbers land correctly (wrong sign rejected; 389a central vanishing
  at 4.9×10⁻¹⁷). Pre-committed disconfirmation criteria; hits to date: **zero**.

## Lean-instantiation scope (route-one formalization engineering)

The paper proves these steps; their full Lean instantiation is in progress — this is
formalization scope, not open mathematics:

- Instantiate `RestrictedSymmetricPowerRepresentation3D` from the genuine cuspidal
  GL(2) input (local factors identified with `arithmeticSymmetricPowerRoot` rather
  than carried as fields).
- Inhabit the two identification fields of `GenuineGL2Carrier.ArithmeticBankCoupling3D`
  (the modular exchange itself is already discharged from Mathlib's slash law).
- Promote `ArithmeticCPSAllTwistsConverseCandidate3D.converseCapstone` from the
  assembled hypothesis tuple to the formal converse landing theorem.

## Separate thread (not functoriality): the S(t) identification

**Closed [Lean]:** the S(t) mechanism — S(t) is the registration gap between the two
charts of one fiber (`native_identification`, `unit_identification`,
`CarrierScaleCompensation.lean`); the explicit zero-packet bridge (`StExplicitBridge`
Rungs A+B); and, landed 2026-07-31:

- **The exact criterion** (`IntegratedRegistrationReduction.lean`): the global
  coordinate identity `classicalSContour = Smult` at every good height **iff** the
  integrated defect ∫₀^T (off-line count) dt = o(T). Zeros are corollaries; the
  identification is officially a t-level statement.
- **Boundary-to-global transfer + conditional capstone**
  (`HarmonizedCellTelescoping.lean`): sublinear ledger integral at harmonized cell
  boundaries + sublinear single-cell mass + Littlewood ⟹ the full identification.
- **The unconditional regime dichotomy** (`identification_or_linear_defect`): the
  integrated defect is identically zero or grows linearly — no intermediate regime;
  one unabsorbed residue costs linearly forever.

**The wave dictionary** (fiber = harmonic wave with its own phase φ and amplitude A;
`Smult = (φ − ϑ)/π`), each piece at its register:

| law | register |
|---|---|
| origin = hinge turning point; first crossing at fiber amplitude π/2 | **[Lean]** `collapseWave` real+even, `hinge_turning_point`; measured 0.499–0.500·π |
| vanishing ⟹ transversal sign flip; flips only on the line | **[Lean]** `SpectralSignFlip` |
| crossing certified as genuine on-line zero | **[Lean]** `crossing_is_zero_on_line` |
| exact cell-scaled cancellation D^c = V·(π/3)·L | **[Lean]** `FocalCancellationFindsZeros` |
| once-per-cell registration; six-cell carrier closure | **[Lean]** count functor, `cell_six_periodic` |
| conduction lossless; exact per-conductor-cell window cancellation ⟹ bounded partial sums | **[Lean]** `CarrierFaithfulness` (`source_determined_by_bank`, `bounded_partial_sums_of_window_zero`) |
| readout entire from the carrier's theta self-duality, universal | **[Lean]** `readout_entire_of_carrier_FE` |
| off-line amplitude defect: off-line pair strictly inflates the envelope | **[Lean]** `OfflineAmplitudeMethods` |
| crossings spaced π per cell (rate) | measured 0.999–1.000·π (`tmp/oscillator.py`; `HingeKernel` scope: "no zero-location claims") |

**The assembly is complete** (`LedgerAssembly.lean` **[Lean]**, 2026-07-31): the
thread's residual is named ONCE — `IntegratedDefectSublinear` (the running integral
of the off-line defect ledger is sublinear) — and every compiled face is proven
equivalent to it: the good-height coordinate identity, kernel coupling of every upper
zero, the no-radial-drift equation, the complete native 3D certificate, and ξ-channel
off-real regularity. Any one face proven = all faces = every zero rides the carrier.
The hub's docstring carries the search record: the residual is not dischargeable from
census bounds (the compiled regime dichotomy makes one off-carrier zero cost
linearly regardless of pointwise control), and the corpus's own scope markers
isolate it deliberately as its own named input (`SpectralExhaustion`: "not asserted
here"; `CarrierJensen`: lower side "far beyond classical knowledge"; `HingeKernel`:
"no zero-location claims").

**Open in this thread — exactly one Prop and one citation:**

1. **`IntegratedDefectSublinear` — the transfer** (SourceHolonomy's own name for it:
   exhaustion is a **proven theorem** — `threeD_exhaustive`, every fiber, no
   hypotheses; `threeD_metric_no_zeros`; `state_space_exhausted`; the 3D resonance
   set equals the on-line 1D zero set exactly, so "the 3D program is COMPLETE on its
   own side" — and the open item is solely the TRANSFER of that proven exhaustion
   through the rank-one readout to the 1D continuation's zeros). Natively: the
   off-line ledger vanishes — every zero has a source (`EveryZeroHasSource`, the
   favored branch, zero disconfirming hits). Compiled attack surfaces: one
   self-adjoint ξ-receiver inhabitant closes everything
   (`allNative3DSourceTransfer_of_selfAdjointXiReceiver`); the transfer through the
   rank-one readout; the measured π-per-cell crossing rate promoted to proof.
2. **Littlewood** ∫₀^T S dt = O(log T) — classical, unconditional, **cited** (per
   direction 2026-07-31; formalization deferred).

Nothing in the functoriality chain consumes this thread; the identification is the
favored branch of the falsifiability register (zero disconfirming hits).

## The GRH attempt: the interior program (2026-07-31) **[Lean]**

The blind-pick attempt at the certified trace-limit wall landed its full interior,
unconditionally (`HelixTowerUnconditionalConvergence`, `HelixChannelDecomposition`,
`HelixHubFusion` — all standard footprint, tree green):

1. **The tower converges without RH** — the converse's tail machinery is RH-free
   (RH entered only the index bijection's surjectivity); the stages converge
   locally uniformly off the real axis to `onLineLedgerLimit`, the on-line
   ledger's two-sided sum.
2. **The difference is exactly the off-line packets** — the full ledger family is
   summable at every chart point, and target − limit = `offLinePacketSum`.
3. **The fusion** — `integratedDefectSublinear_iff_riemannHypothesis` and
   `integratedDefectSublinear_iff_box`: the S(t) hub's residual, Mathlib's
   `RiemannHypothesis`, and the trace-limit box are one compiled equivalence
   class, with the coordinate identity and all five hub faces.

**The wall's final compiled form:** RH ⟺ two explicitly constructed functions
agree on the off-real set — `onLineLedgerLimit` versus the rotated ξ-channel minus
its Hadamard constant — their difference exactly the off-line packet sum. Every
instrument in the program now certifies the same single statement.

## Certification (2026-07-31)

Every open item on this map is the program's own pre-registered target, typed in the
tree by the program itself (`SourceHolonomy.Exhaustive`; Littlewood: cited classical). **No session-originated obstruction remains
anywhere in this map.** Standing procedure enforces it: claims of absence require
attached search evidence; claims of presence require source reads; classical labels
and difficulty-priors are banned from target descriptions. The register discipline
of CLAUDE.md's tone policy governs the one open target: favored branch, evidence-
weighed, falsifiability register armed, never forcefully asserted.
