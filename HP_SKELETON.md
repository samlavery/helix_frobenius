# HP_SKELETON — the Hilbert–Pólya proof plan in the lifted geometry (rule 11 artifact)

Written 2026-09-01 after reading, at source: `RH_LEDGER.md` entries 1–515,
`automorph/hp_pencil.tex` (full), `automorph/universal.tex` (Part I, the S(t) part,
the meta method, worked example, conclusion), `automorph/grh_companion.tex` (HP setup,
theorem list, Proofs A and B, conclusion), `automorph/hodge_companion.tex` (intro,
findings, terminus, path to proof, conclusion), `C3_SKELETON.md`, and the 2026-08-31
door files (`BankLimitBridge`, `BankHerglotzReduction`, `BankNoTransient`,
`PrimeClockCentered`, `PrimeClockDoor`, `EtaLogDerivBank`, `SeatingStageDoor`,
`HPHelixSupply`, `FiniteBankMass`).

Supersedes the ROADMAP header of `C3_SKELETON.md` as the governing plan. C3 keeps the
road-by-road record; this file keeps the proof plan.

**Update law (rule 11):** every session either fills a node here or refines this file.
Work with no slot here is named as such before it is done. Any node claimed open carries
a ledger number and a compiled theorem name, or an explicit "grep returned none."

---

## 0. The instrument decision (Sam, 2026-09-01)

Asked where the registration identity should be exhibited — through the heat balance
(ends against winding), through a readout limit of prime clocks, or elsewhere — Sam
answered: **focal cancellation and an eigenvalue.**

Reading: the identity is SPECTRAL. Every vanishing of the fiber is a focal cancellation
at an eigenheight, and that eigenheight is an eigenvalue of the carrier operator. The
proof is the identification of the two, not a limit and not an estimate. This is Road C
of `C3_SKELETON.md` and the HP capstone's "one box = the seating"
([[hilbert-polya-capstone]]), and it is the direction of this plan.

The proof in its native direction (3D → 1D), each step with its compiled anchor:

1. **Lift.** The fiber IS the L-function: readout converges on Re s > 0 to the continued
   L, and L is the unique entire extension (`DirichletFiberEquivalence`,
   `UniversalFiberEquivalence`, `PrincipalFiberEquivalence` via eta conduction). No
   lifting problem exists.
2. **Geometry.** Double-ended Archimedean helix + conjugate anti-helix through the
   origin, exchanged by J. FE = J read through the projection, no Poisson. The balanced
   abscissa is derived: carrier radius ~ √n balances amplitude n^{−σ} only at σ = ½
   (`carrierScaleBalanced_iff`, `carrierAbscissa_eq_half`). No-drift ⟺ balanced
   (`noRadialDrift_iff_carrierAbscissa`).
3. **Constitution of the bank.** Three things only: the two ends, the carrier winding
   (wind(mn) = wind(m) + wind(n) — Euler lives in the helix), the strand pairs with
   determinant one. Vanishing IS focal cancellation of the P/M channels at an eigenheight
   ([[vanishing-is-constitutive]]): a definition, not a mechanism.
4. **Operator.** On carrier states the height operator is diagonal and symmetric, every
   carrier state an eigenvector with real eigenvalue log Z
   (`carrierThreeDOperator_isSymmetric`, `_eigenvector`). Per prime clock the unimodular
   face is a unitary twist = self-adjoint generator; the finite bank supplies HP at every
   finite rank (`finiteBank_hp_supply`). Zero-ledger decomposition compiled:
   `H_ξ = H_carrier − i·D_radial` (`xiZeroLedgerOperator_eq_height_sub_I_smul_radialDrift`).
5. **Project.** 3D→2D drops radius through Cayley (booked); 2D→1D drops angle (booked);
   projection with ledger is a bijection (`ConeProjection.record_bijective`). An
   eigenstate at height Z reads at ½ + i log Z. S(t) is the registration gap between the
   π/3 carrier and the unit chart (`carrier_scale_compensation_S`).
6. **Conclusion.** Every focal cancellation is an eigenstate of a self-adjoint operator
   at a real height, and the projection reads it on the line.

**The one step, named natively:** REGISTRATION, not coverage. The chart books every focal
cancellation at the balanced abscissa. Three compiled faces of the same identity:
- ledger face — the radius entry booked at 3D→2D is trivial at every vanishing;
- operator face — `D_radial = 0` on the vanishing set, basis mode by basis mode
  (`xiZeroLedgerResidual_eq_zero_iff_each_basis`, no summed-trace cancellation possible);
- bank face — the completed clock product's focal cancellations inherit per-clock
  drift-freeness (compiled at finite rank: `finiteBank_seatMass_nonneg`,
  `carrier_zeros_real`).

---

## 1. The skeleton (backward from the target; tags per rule 11)

```
[RH]  RiemannHypothesis (Mathlib prop, ZD.NontrivialZeros constant verified)      TARGET

  EXTRACT — compiled doors, all {propext, Classical.choice, Quot.sound}
    riemannHypothesis_of_eigenvalue_correspondence   HPCorrespondenceDoor           COMPILED
    riemannHypothesis_of_box_mass_registration       SeatingRegistrationDoor        COMPILED
    rh_of_selfAdjoint_resolventReadout_xi            HilbertPolyaCapstone           COMPILED
    rh_iff_symmetrizedLineTower_traceLimit           companion §conclusion          COMPILED EQUIV
    riemannHypothesis_of_channel_mass                SeatingMassRH                  COMPILED
    riemannHypothesis_of_stage_mass                  SeatingStageDoor               COMPILED
    riemannHypothesis_of_bank_convergence            BankLimitBridge                COMPILED
    riemannHypothesis_of_herglotz_sum_convergence    BankHerglotzReduction (D8)     COMPILED
    rh_iff_online_above_58 ; seating_below_ladder    DVPChannelBase / ladder 634.5  COMPILED

[E3]  THE SEATING — THE LEAF.  Focal cancellation = eigenvalue, for EVERY zero:
      ∀ ρ ∈ NontrivialZeros, ∃ completed focal event e on the carrier with
        carrierPointAtHeight Z_e = ρ  and  multiplicity = xiOrderNat ρ.
      Compiled interface: SpectralCarrierKernelCoupling3D ; nonempty_coupling_iff
        (a coupling exists ⟺ the analytic kernel and the carrier coordinate name the
         same point ⟺ Re ρ = σ*)                                                  ledger 286
      Three compiled registers of the SAME node (do not count them as three problems):
        count   N_off ≡ 0                offLineMassLog_iff_offLine_zero        ledger 424, 426
        trace   windowed exhaustion      traceLimit_of_rh (converse compiled)   companion
        mass    seatMass ≥ 0 on channel  channel_mass_iff_online                SeatingMassPositivity
      TAG: EQUIV (= RH) by nonempty_coupling_iff.
      SHAPE: constructive — an object to exhibit per zero, discharged by identity
             if and only if the identification theorem is proven.  That theorem is RH.

  REGISTER — compiled identities that feed E3
    classicalSContour_eq_Smult_add_offLine  (S_Γ = S_mult + N_off^mult, exact)  COMPILED
    ledger_balance_constant_free            CarrierLedgerBalance                 COMPILED
    gramH_rank_drop_iff_L_zero ; pencil_sees_registered_vanishing (every height) COMPILED
    xiZeroLedgerOperator_eq_height_sub_I_smul_radialDrift                        COMPILED
    half_flips_per_box (density ½) ; seating_density_floor (Zeta23 2/3)         COMPILED partial
    odd_mult_flips (every odd-order on-line zero flips)                          COMPILED

[E2]  THE OPERATOR — H = carrier height on the event space, symmetric by construction
      carrierThreeDOperator_isSymmetric / _eigenvector ; finiteBank_hp_supply    COMPILED

[E1]  THE SPACE — one basis vector per focal event, norm² = multiplicity,
      definite by construction (sum of squares)
      SeatingLedger booking ; pairForm_online_pos                                COMPILED

  LOAD — multi-rail
    rail 1  the ζ fiber, readout = ζ via eta conduction                          COMPILED
    rail 2  finite clock banks ∏ symClock: zeros real, seat mass ≥ 0 by identity,
            Herglotz closed form (symClock_logDeriv_closed,
            bank_readout_logDeriv_closed, finiteBank_logDeriv_expansion)        COMPILED
    rail 2 as a READOUT LIMIT on the channel                                     DEAD — see §2

  GEOMETRY  helix + anti-helix, J, area law σ* = ½, no-drift ⟺ balanced          COMPILED
  LIFT      fiber equivalence, all three families                                COMPILED
```

**Guard verdict (rule 11).** E1 and E2 are compiled and constructive. E3 has the
constructive SHAPE the guard demands — an object exhibited per zero — but its discharge
is the identification theorem, and the compiled iff says the identification holds exactly
when Re ρ = σ*. So this file is a proof plan MODULO ONE EXHIBITION, and that exhibition
carries full strength. Every road in the ledger and both papers land there
(ledger 424: "every road's second node IS the theorem"). That is reported, not
manufactured. Rule 0: strength is a reason to attempt, never to stop.

---

## 2. What the ledger settles — do not re-walk (cited)

- **Height rungs cannot close the seating.** Ledger 494: conjunct 1 closed at the first
  rung (`online_below_58`); every rung since widens a bounded region; the seating
  quantifies over an unbounded set. The ladder is a floor, not a route.
- **The seat transport must cross a collision.** Ledgers 496–497: `det H = (∏w)·disc`,
  `sign(disc) = (−1)^{r₂}`, the crossing is transversal and codimension one within the
  moment family. Refutation spec issued at 499 (`tmp/spec_collision_wall.md`).
- **Steering is dead.** Ledger 215: terminal fixity forces self-resonance.
- **The seat is equivalent to q(W) = 0, not stronger.** Ledger 284 (given rank M = N).
- **The prime-clock bank is not a convergent readout on the channel.** Raw bank:
  `no_positive_primeToothNoTransient` (compiled 2026-08-31; DC Σ log p/2 diverges, and the
  DC IS the positivity). Centered bank: `PrimeClockCenteredNoTransient` reduces (compiled
  `_iff`) to convergence of Σ Λ(n) n^{−u} at Re u ∈ (0, ½), which would make ζ′/ζ
  holomorphic on a half-plane containing on-line zeros — false for every face assignment
  by coefficient uniqueness. NOT yet compiled; **refutation spec owed** (rule 10):
  partial sums at u = 0.3 − 1000i to 10⁷ terms, predicted to oscillate with amplitude
  growing like N^{0.2}. The eta bank (`etaXiBank_tendsto_on_channel`, built 2026-09-01)
  converges on the channel and carries no sign. Multiplicative = positive and divergent;
  additive = convergent and unsigned. Both faces compiled; the seat is their marriage.
- **The measured lane-balance (P=M) law is a registration echo.** Ledgers 153–154: the
  cross-clock control was well powered (+53σ linear); the sector functional retains only a
  faint nonlinear echo of the linear strain correlation. The Lean planks
  (`ZetaSectorBank`, `zeta_ne_zero_of_imbalance_persistent`) are valid conditional
  formalization; no new information demonstrated.
- **The formal corpus never instantiated the focal geometry at ζ.** Ledger 147:
  `ThreeDExhaustive` is a tautology; the focal chain carries `hχ ≠ 1`. Corrected at 148:
  incompleteness, not refutation. The angle-sector law (149) is the right object; its
  proof status at ζ is open.
- **Analytic-bound routes circle.** Ledgers 512–513: every estimate on ξ′/ξ in the strip
  needs a proviso equal to the conclusion. Geometric inputs are a DIFFERENT kind —
  completeness statements discharged by identity — and the estimate-circle says nothing
  about them.
- **Jensen central rungs are downstream of zero verification.** Ledger 275 (GORTTW:
  d ≤ ⌊T⌋²); the instrument is blunt (Farmer). Do not climb the centre.
- **The HB companion route converges to the classical LP equivalence.** Ledgers 181–184:
  the natural strands are not HB; E = A + iεA′ HB ⟺ RH. The field m(z) = −Im(A′/A)
  measured positive at 100% of points, min(m)/y = 0.0464 constant.
- **Certificate-arena instruments cannot see E3.** Ledgers 106, 128, 146: band-limited,
  one-point, finite-moment certificates reduce to F(α) beyond bandwidth 1; HP is
  structure identification, a different arena; information count is the wrong currency
  there in both directions.

**Calibration laws that bind this plan** (all earned in the ledger):
- the EQUALITY TEST before any "new" object (ledger 272, 514) — does it EQUAL something
  compiled under another name?
- OBSTRUCTIONS CARRY THE BURDEN OF PROOF (ledger 176): pencil → adversarial numeric →
  source check, before any stop-claim; refutation spec for a no-go (rule 10);
- the T-POWER AUDIT (ledger 066): no "the gap is now a constant" without the explicit
  T-dependence;
- EQUIVALENCE IS NOT CIRCULARITY (ledger 229): an iff is a target;
- INTERFACE INHABITABILITY (ledger 147): instantiate every hypothesis at ζ before pricing
  a brick as compiled;
- the RESOLUTION LAW is general (ledger 234): signal = −2y₀²P′(x₀)²/‖c‖², and detection
  needs precision = dynamic range + 2 log₁₀(1/y₀) + Christoffel;
- an FE-respecting adversarial object is a QUADRUPLE in the w = z² quotient chart, never a
  bare pair (ledger 235).

---

## 3. The plan — four tracks

### Track 0 — housekeeping (one session, certain)

- Commit the 2026-08-31 untracked Lean files (25 files; all oleans fresh;
  `EtaLogDerivBank` built clean at 8799 jobs on 2026-09-01) and the modified
  `SeatingMassDisk`, `XiTailStripBound`, `C3_SKELETON.md`.
- Issue the owed refutation spec for the centered prime-clock bank (`tmp/spec_centered_
  prime_bank.md`), self-contained, decision rule pre-registered, prediction recorded.
- Keep this file current per the update law.

### Track A — the labor package (several sessions, zero mathematical risk)

The C3 roadmap's Phase A, unchanged, in order A3 → A2 → A1:

- **A3** — splice the Γ/pole terms (`logDeriv ξ = 1/s + 1/(s−1) − ½ log π + ½ ψ(s/2) +
  logDeriv ζ`) onto `zeta_logDeriv_eq_etaLim` → `seatMass_eta_form`: the mass hypothesis
  stated entirely in ordered carrier data plus explicit trivial terms. If Mathlib lacks
  complex digamma, use `logDeriv Complex.Gamma` directly.
- **A2** — stage/F holomorphy + derivative transfer (dominated differentiation with the
  compiled u-weighted tail majorants, or Cauchy from the compiled uniform rate). Closes
  `riemannHypothesis_of_stage_mass` clause (ii).
- **A1** — L1b identification `xiIntegral(z) = ξ(½ + iz)`: Mathlib's
  `completedRiemannZeta₀` is the Mellin transform of the theta kernel; unfold (symmetrize
  by FE, two integrations by parts onto the compiled `riemannXiKernel` shape, t = e^{2u}),
  prove on a real segment, extend by the identity theorem (needs A2). Closes clause (i).

Output: one machine-checked theorem `[ONE hypothesis] → RiemannHypothesis` with the
hypothesis readable in carrier data. Does not touch E3; makes E3 readable where the
Track-B instruments act.

### Track B — the leaf, built in the pencil frame with the 3D lift (the content)

Sam's Gram double pencil is the object where focal cancellation and eigenvalue are the
same event: the rank drop IS the eigenvalue collision at the focal height
(`gramH_rank_drop_iff_L_zero`; `pencilFin_det = (λ−μ)·A·B`). Ledger 108 recorded the
corrected anatomy: G(t) is a PSD trig-matrix family with computable ratio-frequency
entries; det G ≥ 0 with zeros as tangential touches; the AMBIENT DIMENSION is
load-bearing (the 1D scalar collapse makes the lane Gram identically rank-degenerate; the
3D transverse components keep it nondegenerate off events). Ledger 110 built the 2-lane
scalar-adjacent detector, confirmed the P=M shadow at +5.7σ, and found the detector
50× short of resolving an injected drift δ = 0.05 — and specified the fix that was
never built: **the genuine 3D lane vectors** (focal_closure.py `Family` / `lane_key` /
unimodular `u_lane` / lane resultants / `test_lane_balance_at_zero`). Ledger 109: the
conjugate anti-helix + Frobenius make touch depth a ONE-parameter exact functional (the
drift exponent, common to all sites by Frobenius multiplicativity; reflected-pair product
law n^{β−½}·n^{(1−β)−½} = n^{−1} exact).

Three steps, each with a pre-registered kill test.

**B1 — build the 3D lane pencil.** G(t) from the product-form bank at cell scale
(∏ symClock; rank drops real by `carrier_zeros_real`), lane resultants as true 3D vectors
from the Family machinery, coupled to the winding host with its two ends (the
`ledger_balance_constant_free` structure: prime readings = mirror-pair census + ends +
winding). Identity checks FIRST, both mandatory:
  (i) at every on-line zero in the verified range the rank drop is exact;
  (ii) at σ > 1 the renormalized resolvent readout reproduces
       `ledger_balance_constant_free` to 1e−12.
  Failure of either is a BUG, not a finding. Do not proceed past a failed identity.

**B2 — calibrate the contact functional.** Inject an FE-respecting quadruple in the
w = z² quotient chart (ledger 235), never a bare pair. Measure touch depth of det G at
drift δ ∈ {0.05, 0.02, 0.01}; compute the size threshold m = r + 2q of the test
configuration first and set n ≥ m (ledger 235's standing rule).
  Decision rule, fixed now: resolution ≥ 10× the 2-lane result at δ = 0.05
  (2-lane: excess +0.0074 against noise 0.4) ⟹ the 3D lift is load-bearing for detection,
  and the contact functional is the quantity a proof must show vanishes. Below 10× ⟹ the
  lift is not load-bearing at this projection; record, and route to B3 through the
  window-contour chart instead (the well-conditioned γ-side instrument, ledger 208).
  Prediction (recorded before running): resolves materially better than 2-lane, still
  short of proof grade; the yield is the explicit cosh-drift functional of ledger 109 in
  computable form. The T-power audit applies to any "resolution" claim.

**B3 — state the contact certification as the leaf's Lean interface.** Every ξ-zero is an
EXACT TOUCH of G, never a near-touch. This is E3 in pencil coordinates. Compile the
interface first (the shape of `riemannHypothesis_of_real_staged_cascade`: `converges` for
the pencil/sum staging ✓ compiled; `hreal` for product-form banks ✓ compiled; the two
fields fed by the two compiled halves — C3_SKELETON "PENCIL JOIN READING"). Then the
proof-side content: the touch-versus-near-touch dichotomy is a positivity-depth statement
on a matrix family with computable entries. Ledgers 229–231 measured where window
positivity comes from: the ARCHIMEDEAN block (the two ends) supplies it, the prime block
is negative on the near-null direction, the boundary drains. So the certification must
consume ends and winding together — exactly the constitution's three fields.

### Track C — the seating in the count register (parallel)

`classicalSContour_eq_Smult_add_offLine` makes E3 read as `N_off ≡ 0` above 634.5
(ledger 424/426: the register road collapsed to this one node). Compiled partials:
`half_flips_per_box` (flip visibility at density ½), `seating_density_floor` (Zeta23 2/3),
`odd_mult_flips` (odd-order on-line zeros always flip). The flip-invisible classes are
EXACTLY off-line zeros and even-order on-line zeros (C3 Road C, "LEAF SHARPENED"). The
leaf here is upgrading the flip census to density one per box. Any touch certified in
Track B at a height is a flip at that height; the two tracks feed ONE ledger.

### Track D — falsification (standing, published either way)

- any measured m(z) = −Im(A′/A) < 0 at verified precision (ledger 184);
- any negative Hankel inertia at a real window in the FE-respecting Stieltjes pair
  (ledger 193, 235) — the census is exact, precision per the resolution law;
- any depth-ladder counterexample (`depth_criterion_iff`, ledger 297): a zero with
  |β − ½| > d together with anchor positivity at depth ≥ d;
- the falsifiability register of the papers (non-collapsing arch floor, non-Euler
  spectral line, phase cell ≠ π, weight-law violation, configuration-universality break).

---

## 4. Calibration

- This file is not a proof. It is the skeleton with every node cited, one leaf named in
  the house register, and a construction sequence for the leaf that uses only moves the
  ledger has not tombstoned.
- E1, E2 compiled. E3 EQUIV to the target by compiled iff. Its shape is constructive; its
  discharge is RH. Rule 0: attempt it. Rule 9: build toward it; blocks must be
  ENCOUNTERED in B1–B3, then routed around, then verified by the full ladder before any
  entry records them.
- Track A's theorem is certain and does not move E3.
- Track B's B1–B2 are measurements with pre-registered decision rules; B3 is where the
  arithmetic must enter and where every prior route in the ledger terminated. If B3
  terminates the same way, the entry says so at exactly that strength, with the
  encountered block named, and the plan is refined here — not softened, not inflated.
- The Hodge companion's terminus architecture is the template for the shape of E3:
  `SourceExhaustion = Retention ∧ Recognition`, compiled exact and independent
  (`sourceExhaustion_iff_recognition`, `factorization_exact_and_independent`). Here
  Retention is E1+E2 (no silent event: every focal cancellation is an eigenstate) and
  Recognition is E3 (every zero is a focal cancellation). Recognition is the theorem in
  both programs.

---

## 5. Index of compiled objects this plan consumes (grep before citing; verify axioms)

Doors: `HPCorrespondenceDoor`, `HPRankDropCascade`, `SeatingRegistrationDoor`,
`HilbertPolyaCapstone`, `SeatingMassRH`, `SeatingStageDoor`, `BankLimitBridge`,
`BankHerglotzReduction`, `PrimeClockDoor`, `DVPChannelBase`, `SeatingLadderFold`.
Registration: `ZetaContourArgument`, `CarrierLedgerBalance`, `PencilCellEdgeDoor`,
`XiZeroLedgerResolvent3D`, `SpectralCarrierKernelCoupling3D`, `ZetaContourCouplingDefect3D`,
`ZetaContourGlobalIdentification3D`, `SeatingLedger`, `SeatingHalfFlips`, `SeatingFloor`,
`SeatingOddFlips`, `DVPOffLineIff`.
Operator/space: `CarrierUnboundedResolvent3D`, `FoliatedPolarization`,
`FoliatedGlobalPolarization`, `FoliatedDeterminant`, `HilbertPolyaResolventTrace`,
`HPHelixSupply`, `HelixWarpCovariance`.
Banks: `FiniteBankMass`, `BankNoTransient`, `PrimeClockCentered`, `PrimeClockOrdering`,
`PrimeClockData`, `EtaLogDerivBank`, `CarrierChannelReadout`, `CarrierTransientRigidity`,
`CarrierCarlsonMean`, `DVPCarrierContinuation` (`etaLim_eq_zeta`).
Seat: `SeatScalarCriterion` (`seat_criterion_iff`, `depth_criterion_iff`,
`seat_energy_ge_window`), `DVPSeatRungOne`, `DVPSeatResonance`, `SeatingMassDisk`,
`SeatingMassLedger`, `SeatingMassPositivity`, `SeatingMassWrap`, `DVPSeatRealPart`,
`XiStructureHBSeat`, `XiStructureNativeSeat`.
Stages: `XiTailStripBound` (`xiStage_tendsto_xiIntegral`, `xiStage_extent_hasDerivAt`),
`SeatingDeepPairBound`.
Numerics: `focal_closure.py` (Family/lane machinery), `tmp/att110_detector.txt` (2-lane
baseline), `tmp/att185b_grampencil.txt`, `tmp/att187_decomposition.txt`,
`tmp/att224`–`att233` (census controls), `tmp/att184c_confirm.txt` (m(z) field).

Papers: `automorph/hp_pencil.tex` (Theorems inertia/census/Stieltjes, the operator
reading, the seat split), `automorph/grh_companion.tex` (the three operator levels,
`grh_of_selfAdjoint_resolvent_capture`, `rh_iff_symmetrizedLineTower_traceLimit`),
`automorph/universal.tex` (Part I, §carrier-S, the meta method).
