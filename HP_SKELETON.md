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

**Refined 2026-09-01 (ledger 517, Sam's go-ahead on items 1–3):** Track B retagged as an
INSTRUMENT track after the equality test (four hits, listed at Track B); its route-around
struck (Taylor); the clock door's admissible class compiled (`BankDoorClassLaw.lean`, six
theorems, standard axioms) and entered in §2; the guard verdict of §1 unchanged.

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

### 0a. The geometry, canonical — Sam, 2026-09-01 (verbatim, lightly punctuated)

> Double-ended helix, is conjugate. Carrier rides both sides and is scaled harmonically.
> The L-function is the fiber and it rides the carrier. It is warped to vanish at the
> harmonic cell edges and leaves no residue when it vanishes. It creates the eigenvalue at
> some height; that height corresponds to the analytic zero ordinate — not equal to, but
> coincides with it. It uses focal cancellation from the fiber's banks, uses phasors that
> rotate.

This is the frame every node below is read in. Clause by clause, the compiled object each
names (all grep-verified 2026-09-01; axioms standard unless marked):

| clause | object |
|---|---|
| double-ended helix, conjugate | `C = C₊ ⊔ C₋`, anti-helix = transverse phase reversed, `J` with `J² = id` (universal.tex thm:g1-double-carrier); FE reflection is the end-swap, involutive: `feReflect_involutive` |
| carrier rides both sides, scaled harmonically | same radius and height laws on both lanes, only the phase sign differs (thm:g1); the scale is a harmonic constant on the carrier's own lattice, `Admissible.scale`, readout-invariant: `vanishing_preserves_readout`; gauge `x_n = (π/3)n`; the harmonic register law (CLAUDE.md) |
| the L-function is the fiber, riding the carrier | `DirichletFiberEquivalence`, `UniversalFiberEquivalence`, `PrincipalFiberEquivalence`: fiber readout and L are equivalent representations; the source occupies the carrier through its fiber (universal.tex thm:g3-g4) |
| warped to vanish at the harmonic cell edges | warp = unit-modulus reparametrization, `warpFiber`/`DualWarp`; per-cell closure is forcible by real warp weights, `ForcibleClosure.residual_forcible`; the fiber converts any scale into the native harmonic walk, `dressedCell_eq`, `fiber_converts_to_harmonic`, `every_scale_admits_conversion`; the cell edge is the μ6 wall, one per closed 6-loop at `k ≡ 3 mod 6`, `pi3_arcs_eq`, mark `−1` realized iff `kH = odd·π`, `eventArcs_nonempty_iff` |
| leaves no residue when it vanishes | `B(Z) = (π/3)·L(½ + i log Z)` identically, `cell_normalized_scalar_exact`, `Ucell_ne_zero`, `scalar_zero_iff_L_zero`; μ6 blocks close exactly in `ℤ[ζ₆]` (`exact_cell_marker`, integer arithmetic); law: cells have no residue, a cell BOOKS its ledger entry ([[vocabulary-cells-no-residue]]) |
| creates the eigenvalue at some height | the completed event at physical height `Z` is an eigenvector of the ambient carrier operator with eigenvalue `log Z` and zero radial drift: `completedThreeDZeroAtHeight_focal_rankDrop_eigenvector_noRadialDrift`, `threeDZero_ambientEigenvector_resolventTrace`; the fibre operator is symmetric by theorem, `vonNeumannOp_isSymmetric` |
| height corresponds to the ordinate: not equal, coincides | `carrierPointAtHeight Z = carrierPoint (log Z)`, exact conversion `carrierPointAtHeight_exp`; `eventHeight_eq_focalCancellationHeight`; the ordinate is the READOUT of the height in another chart, and projection with its loss ledger is a bijection, `record_bijective`; same readout ≠ same state (universal.tex cor:g2-projected-equality); the two charts are registered, and `S(t)` is exactly their registration gap, `carrier_scale_compensation_S`; the carrier's image is the line by the area law, `carrierScaleBalanced_iff`, `carrierAbscissa_eq_half`, `noRadialDrift_iff_carrierAbscissa`, `exists_eq_carrierPoint_iff` |
| focal cancellation from the fiber's banks | `focalClosure_iff_rankDrop`, `completedThreeDZeroAtHeight_iff_L_zero`, `principalZero_focalCancellation_on_carrier`; finitely, P = M lane balance with each lane O(1)-large (`test_lane_balance_at_zero`; att518: lanes 1.08 and 4.32 against closures 1e−6 and 3e−12) |
| phasors that rotate | head-coupled readout angle `θ_n = −y·log x_n` (`resonanceHeightEquiv`, HeightGrowthActive); born at magnitude 0 and grown (`growth_window`); the clock face `e^{izℓ}` (`symClock`); rank drop is rotation-driven interference of lane resultants (ledger 108) |

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

## 1. The skeleton (backward from the target; tags per rule 11) — HP form, 2026-09-02

Sam, 2026-09-02: "we prove offline zeros can't exist in this program already, can we just
focus on HP?" — compiled as `not_scaleBalanced_of_ne`, `no_offCarrier_representation`,
`exists_eq_carrierPoint_iff`, `no_offCarrier_completedFocalCancellation` (an off-line zero is
not a carrier state or event). The analytic identification the companion lists as its
interface is discharged BY the HP object through the capture door, so the plan is HP.
Also fixed by Sam the same day: no off-line fibers exist on the helix (X-drift struck), and
the warp removes the S(t) correction so vanishing is residue-free at a cell boundary
(compiled: `carrier_scale_compensation_S`, `Sgap_pi_div`, `unit_arcs_empty`,
`cell_normalized_scalar_exact`, `residue_eq_Smult_jump`).

```
[RH]  RiemannHypothesis (Mathlib prop, ZD.NontrivialZeros constant verified)      TARGET

[HP]  ONE fixed self-adjoint operator a, built from carrier + fiber with NO zero set in its
      definition, whose resolvent readout is the completed channel
      T(z) = −ξ′/ξ(½ + iz), regular off spectrum(a).
        ⟹ GRH   grh_of_selfAdjoint_completed_resolvent_capture                    COMPILED
        ⟸ RH    selfAdjointReceiver_xi_iff_rh  (exactness: no slack)               COMPILED
      TAG: EQUIV to the target at exactly its strength; the OBJECT is the exhibition.

  [HP-space]  CarrierThreeDMode p r = CarrierState3D p r →₀ ℂ (all carrier states, height-
              indexed); the completed-event subtype; event basis, norm² = multiplicity     COMPILED
  [HP-op]     A⁽³⁾ = carrierThreeDOperator = diag(ordinate): symmetric, every carrier state
              an eigenvector; the completed event SELECTS its eigenstate and does not define
              the operator (carrierThreeDOperator_completedEvent_eigenvector); finite unitary
              banks supply a symmetric operator with all their zeros as eigenvalues
              (finiteBank_hp_supply, carrier_zeros_real)                                COMPILED
              Read against [HP]: spectrum(A⁽³⁾) = ℝ, so capture for A⁽³⁾ is exactly
              "T has no pole off the real axis" — the companion's "one remaining closure
              step is the operator" is this sentence.
  [HP-trace]  zero side: hilbertPolya_resolvent_trace (two-point), xi_spectralCoord_mem_
              singularSupport, completed_logDeriv_not_tendsto (completed resonance: the
              interface is satisfiable in principle), rh_iff_symmetrizedLineTower_traceLimit.
              fiber side: seatMass_eta_form (channel: ends + Γ-clock + logDeriv of the ordered
              readout), logDeriv_riemannXi_arith (Re s > 1), zeta_logDeriv_eq_etaLim.
              clocks (2026-09-01): door admits pole swarms only (BankDoorClassLaw, 517);
              Euler face = Poisson barycenter of unitary faces on the RIGHT, anti-Euler face
              r⁻¹ on the LEFT (ClockPoissonBarycenter, 520); small winding = Hadamard atom
              (ClockSmallWinding, 521)                                                  COMPILED
  [HP-LEAF]   the readout identity from the fiber alone — THE MARRIAGE OF THE TWO FACES.
              Multiplicative face (unitary-clock barycenter operator): signed, real-rooted,
              DC divergent on the channel (no_positive_primeToothNoTransient).  Additive face
              (closed-cell ordered bank, eta conduction): convergent on the channel, unsigned
              (etaXiBank_tendsto_on_channel).  Compiled at ONE conduction prime:
              zeta_logDeriv_eq_etaLim = ζ′/ζ = (ordered bank at 2)′/(…) − (anti-Euler clock at 2)′/(…).
              INSTRUMENT att530 (ledger 530) RUN: at every window on the channel the clock
              (barycenter) face contributes NEGATIVE seat mass with DC Σ_{q∈Q} log q, the
              closed-cell ordered face contributes the compensating POSITIVE mass and holds all
              the zeros' poles; the door-law floor holds on the barycenter face (slack −0.059);
              the closed-cell bank converges at rate N^{−σ}. The marriage = a DC subtraction
              (cell closure removes the clocks' DC) — the operator must be built as
              "closed-cell face minus clock DC" (Q = {2} instance compiled:
              zeta_logDeriv_eq_etaLim).
              COMPILED 2026-09-02 (ledger 531): the door-law floor for EVERY face ‖α‖ ≥ 1
              (BankDoorFaceLaw: clockFace_logDeriv_re_le, bankFace_logDeriv_re_le,
              antiEulerFace_logDeriv_re_le) and the finite-Q marriage identity
              (FaceMarriageIdentity: closedCellBank_marriage, logDeriv_zeta_add_reflected,
              logDeriv_conductionClock, conduction_face_hasSum):
              logDeriv(closed-cell bank)(s) + Σ log q = −(E(s)+E(1−s)) − [logDeriv ζ(1−s) + P_Q(1−s)].
              MEASURED (att531): the marriage has THREE DCs — clock Σ log q, the END term
              Q^{1−w}/(1−w) (the pole at s = 0 read at the cutoff), the Γ/ends pair — and the
              remainder decays like Q^{σ−½} (fitted −0.053/−0.104 vs predicted −0.05/−0.10):
              the zeros' content, separated. Q → ∞ of the corrected defect = the reflected
              explicit-formula convergence = RH (EQUIV register; not progress).
              BUILT (att532, ledger 532): the marriage object in the density register,
              D′_Q = ϑ′/π + DC_Q − ρ_Q^{clock} + END_Q (Γ-clock density, minus the DC-subtracted
              barycenter-clock density, plus the end term Q^{½−iz}/(½−iz)/π), constructed from
              the prime side alone: window counts within 0.02 of one and peaks within 0.015 of
              the zeros at Q = 10⁵–10⁶; the finite-Q measure is SIGNED with bounded negative
              mass ≈ 0.4–0.55 per window (Krein at every stage, Hilbert only in the limit).
              CORRECTED 2026-09-03 (ledgers 567–568): the negative mass is the sharp window's
              Dirichlet lobes, a universal constant of the window SHAPE (Selberg 0.218, cubic
              0.185, sharp ~(2/π²)log V), forced by any plateau at the front (Bochner). With the
              RIESZ window (1 − log n/log x)₊ the kernel is Fejér and the finite-stage measure is
              POSITIVE at every front (att567: negative mass 0.00000 at x = 10²,10³,10⁴).
              RH ⟺ D_{R,x} ≥ 0 ∀x,t — property (i) of the compound object at finite stage;
              `RieszTruncatedFormula.lean`.
              Two DCs alone DIED at Q ≥ 10⁵ (the end term, omitted twice this day: law
              `end-term-dc-law`). The Q → ∞ limit's support on the real axis is RH.
              COMPILED 2026-09-02 (ledger 533, ClockSpectralDensity): clockDensity p z =
              (log p/2π)·Poisson(p^{−½}, e^{iz log p}) = (1/π)Re logDeriv_s(clock face)(½+iz)
              (clockDensity_eq_re_logDeriv); DC split clockDensity − log p/2π = (1/π)Σ_k log p
              p^{−k/2}cos(kz log p) (clockDensity_hasSum); bankDensity − bankDC = Q-smooth von
              Mangoldt oscillation (bankDensity_sub_dc). The marriage measure ν_Q = ϑ′/π + END_Q
              − (bankDensity − bankDC) is now every term named, its clock part proven.
              THE PROOF HALF of this leaf: Weil's explicit formula for band-limited test
              functions (ν_Q integrates bandwidth-≤log Q observables exactly as the zero comb).
              Corpus: NOT compiled (PartialWeilFormula deprecated; WeilContour = Gaussian-pair
              building blocks, identity conditional on the WeilFormula Prop). Multi-session.
              Also open: the finite-Q negative-mass bound; the Krein operator on L²(|ν_Q|).
                                                                                     NOT COMPILED

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

[E3]  THE SEATING — the same node as [HP] in its event register (EQUIV faces; one node):
      Focal cancellation = eigenvalue, for EVERY zero:
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
    clock door admits POLE SWARMS only; prime windings excluded for every
            face / scale / warp (BankDoorClassLaw, ledger 517)                   COMPILED

  GEOMETRY  helix + anti-helix, J, area law σ* = ½, no-drift ⟺ balanced          COMPILED
  LIFT      fiber equivalence, all three families                                COMPILED
```

**Registry cross-reference (Sam, 2026-09-03, ledger 566).** The object IS built: `HP_PROGRAM.md`
§1, the registration operator (diagonal, self-adjoint, spectrum = prime-forced stations,
zero-knowledge-free; measured to RMS 0.039 spacings over 41k zeros, bijectively) and §2 its
compiled certificate `shadowing_implies_online_simple`. The "exhibition" language of this file is
about the EXACTNESS of that object's readout, never about its existence; do not read it otherwise.
The remaining item, in the registry's words: the residual tail law (|γ_n − t_n| < half a gap at
every station), whose exact residual is now the compiled comb of ledgers 563–565.

**Guard verdict (rule 11), 2026-09-02.** E1 and E2 are compiled and constructive. [HP] is
EQUIV to the target with no slack, and its discharge is an OBJECT: the operator whose readout
is the completed channel. The leaf under it is the marriage of the two faces; every other
register (drift, count, trace, mass, receiver, Gram) is the same node and is not counted
separately. Struck 2026-09-02: X-drift (no off-line fibers on the helix — Sam), X-lift (a fifth
register of the count face, ledger 529/530). So this file is a proof plan MODULO ONE
EXHIBITION, that exhibition carries full strength, and the active work is the construction of
the object, instrumented by att530. Rule 0: strength is a reason to attempt, never to stop.

---

## 2. What the ledger settles — do not re-walk (cited)

- **Height rungs cannot close the seating.** Ledger 494: conjunct 1 closed at the first
  rung (`online_below_58`); every rung since widens a bounded region; the seating
  quantifies over an unbounded set. The ladder is a floor, not a route.
- **The seat transport must cross a collision — ADJUDICATED 2026-09-01 (ledger 522), my
  prediction DIED.** Ledgers 496–497 claimed `det H = (∏w)·disc`, `sign(disc) = (−1)^{r₂}`, and a
  TRANSVERSAL crossing. The independent executor refuted (C.2) as worded with two families:
  a double merge (`r₂: 0 → 2`, `det H = 1296τ²(4τ−9)²`) and a merge with a vanishing weight
  (`det H = 4τ²(τ−25)²`); in both, `det H ≥ 0` throughout while two eigenvalues cross zero
  together (verified: n₋ jumps 0 → 2). The det-based transversality claim is FALSE in general.
  What stands is simpler: the seat's criterion is PSD, the inertia theorem makes the negative
  index the number of conjugate pairs, so no PSD path reaches a window with an off-line pair —
  trivially, with no collision analysis. The transport route is a restatement (path exists iff
  `q(W) = 0`), exactly as hp_pencil's rigidity remark says. Do not cite 496's transversality.
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
- **The clock door admits only pole swarms; prime-indexed banks are excluded for every face,
  every carrier scale and every fiber warp.** Ledger 517, `BankDoorClassLaw.lean` (standard
  axioms): `Re logDeriv(symClock)` on the left is `−(ℓ/2)·P_r(θ)` with `P_r` the Poisson
  kernel (`herglotzKernel_re`), so every clock lies below `−clockFloor ℓ σ =
  −(ℓ/2)tanh(ℓ(½−σ)/2)` face-independently (`bank_logDeriv_re_le`); convergence of the bank
  log-derivatives at ONE point left of the line bounds `Σ clockFloor` uniformly
  (`bank_convergence_bounds_floor_sum`), hence boundedly many clocks with `ℓ ≥ ℓ₀` per stage
  (`bank_convergence_bounds_large_clocks`) and bounded stage cardinality for any bank with
  all windings `≥ ℓ₀` (`bank_convergence_card_bounded_of_winding_ge`) — every prime-indexed
  bank. The door (`riemannHypothesis_of_bank_convergence`) is therefore fed only by
  small-winding clocks, each a single pole plus its DC: the Hadamard side, EQUIV. The DC
  `−ℓ/2` is the log of the carrier radius `√p` (unimodular clock = Euler factor + DC; the
  Euler face is the Poisson average of unimodular faces at radius `p^{−½}`, measured 1e−12);
  `Admissible.scale` relabels the lattice and `DualWarp` twists faces, and `clockFloor` sees
  neither. Centering at the END (the pole's main term) lands on von Koch — EQUIV, unsigned,
  outside the door's ∏ shape. The refutation-spec file remains owed (Track 0).
  **COMPILED 2026-09-01 (ledger 520, `ClockPoissonBarycenter.lean`, standard axioms):** the
  Poisson identity is a theorem. `unitaryClocks_poisson_barycenter_right/left`: the Poisson
  average of the unitary clocks over the face circle, kernel centred at `w`, is the clock with
  face `w` (right of the line) or `(w̄)⁻¹` (left). `..._eulerFace / _antiEulerFace`: at
  `w = p^{−½}` these are the Euler factor (zeros on `Re s = 0`, the helix end) and the reflected
  factor (face `p^{½}`, zeros on `Re s = 1`, the anti-helix end). The two ends are the
  face-inversion pair through the unit circle; the critical line is the fixed set of face
  inversion. The Euler product is the Poisson MIXTURE of the pure unitary banks. SHARPENED
  (ledger 520): a torus mixture's trace sees only per-prime marginals, so the operator must carry
  CROSS-PRIME MATRIX ELEMENTS (sums over all `n` inside entries), intertwined by
  `ledger_balance_constant_free` — the constructive target.
  **COMPILED 2026-09-01 (ledger 521, `ClockSmallWinding.lean`):** `symClock_logDeriv_small_winding`
  — with the face pinned at `t₀`, `logDeriv (symClock (e^{iℓt₀}) ℓ) z → 1/(z − t₀)` as `ℓ → 0⁺`.
  The clock door's admissible (small-winding) clocks are the line tower's atoms: the two ζ-doors
  are one object at winding `0` and winding `log p`. The clock family is now fully charted —
  pure unitary / Euler mixture / atom limit — and the operator is none of them per prime.
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

- DONE (in the "universal pdf v0.3" commits; no untracked `.lean` remained on 2026-09-01):
  the 2026-08-31 Lean files and the modified `SeatingMassDisk`, `XiTailStripBound`,
  `C3_SKELETON.md`. NEW untracked, to commit: `RequestProject/BankDoorClassLaw.lean`
  (ledger 517), `RequestProject/SeatMassEtaForm.lean` and `RequestProject/XiStageHolomorphy.lean`
  (ledger 519), `RequestProject/ClockPoissonBarycenter.lean` (ledger 520),
  `RequestProject/ClockSmallWinding.lean` (ledger 521), `RequestProject/ZetaScrewHelix.lean`
  (ledger 523), `RequestProject/ZetaScrewFourier.lean` (ledger 524),
  `RequestProject/ZetaScrewReal.lean` (ledger 525),
  `RequestProject/ZetaScrewArithmetic.lean` (ledger 526),
  `RequestProject/ZetaScrewRamp.lean` (ledger 527),
  `RequestProject/ZetaScrewPrimeSide.lean` (ledger 528),
  `RequestProject/BankDoorFaceLaw.lean`, `RequestProject/FaceMarriageIdentity.lean` (ledger 531),
  `RequestProject/ClockSpectralDensity.lean` (ledger 533),
  `RequestProject/WeilStripContour.lean`, `RequestProject/WeilZeroSide.lean`,
  `RequestProject/WeilPrimeSide.lean`, `RequestProject/WeilExplicitFormula.lean`,
  `RequestProject/WeilTestClass.lean` (Track W, ledger 534),
  `RequestProject/WeilPhasorBank.lean`, `tmp/att537b_phasor_bank_gram_fast.py`,
  `tmp/att537b_results.txt`, `tmp/att537c_diag.py` (Track P, ledger 537),
  `RequestProject/SeatPrimeAnchor.lean`, `tmp/att541_warp_pitch_S.py`, `tmp/att541_results.txt`,
  `tmp/att542_seat_prime_anchor.py`, `tmp/att542_results.txt`,
  `tmp/att543_seat_prime_anchor_dominance.py`, `tmp/att543_results.txt` (Track S, ledgers 541–546),
  `tmp/att530_face_marriage.py`, `tmp/att530_results.txt`, `tmp/att531_marriage_limit.py`,
  `tmp/att531_results.txt`, `tmp/att532_dc_subtracted_operator.py`, `tmp/att532_results.txt`
  (ledgers 530–532),
  `tmp/spec_collision_wall_run/` (ledger 522), `tmp/suzuki_*.pdf` (sources),
  `tmp/att518_lanepencil3d.py`, `tmp/att519_stage_zeros.py`, `tmp/att519b_stage_zeros_mp.py`;
  modified: this file, `RH_LEDGER.md`, `automorph/grh_companion.tex` (the canonical geometry
  paragraph, ledger 518).
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

**A3 DONE, A2 DONE (2026-09-01, ledger 519).** `SeatMassEtaForm.lean`: `logDeriv_Gammaℝ_eq`,
`logDeriv_riemannXi_splice`, `seatMass_eta_form`, `riemannHypothesis_of_eta_mass` — the mass
door restated on `η′/η − (1−2^{1−s})′/(1−2^{1−s}) + 1/s + 1/(s−1) − ½ log π + ½ Γ′/Γ(s/2)`.
`XiStageHolomorphy.lean`: `xiStage_hasDerivAt`, `xiStage_sub_xiIntegral_norm_le`,
`xiStage_tendstoLocallyUniformly`, `xiIntegral_differentiable` (entire),
`deriv_xiStage_tendsto`. Both clean, standard axioms. Remaining: A1 (the identification),
several sessions, EQUIV labor. Calibration confirmed in the doing: A3/A2 make the obligation
exact; they do not build the operator.

**The θ-stage tower is NOT a real-rooted family — KNOWN SINCE 2026-08-31 (C3 [M1-F]:
Csordas et al. 2011 at source; edge-wave front law `x_a(U)`; att565/566/568), re-walked by
att519 on 2026-09-01 (ledger 519 correction).** Each stage `Ξ_U` with `U ≥ 1` carries an escort
pair at the amplitude front (U = 1.0: 31.3 ± 1.1i; U = 1.2: 45.8; U = 1.5: 83.02 ± 0.82i,
40-digit, new). "The pairs escape every compact" is EQUIV to RH by Hurwitz (Haglund's genre),
not STRONGER. The stages are a finite-height certificate instrument (class of 494), not the
leaf. READ `hp-unconditional-campaign` and C3 [M1-F] before any stage work.

Output: one machine-checked theorem `[ONE hypothesis] → RiemannHypothesis` with the
hypothesis readable in carrier data. Does not touch E3; makes E3 readable where the
Track-B instruments act.

### Track B — INSTRUMENT track (retagged 2026-09-01, ledger 517: no proof content)

**Equality test, four hits (ledger 517), visible before further work here:** (a) the compiled
pencil `pencilFin = !![A, B; μA, λB]` has `det = (λ−μ)·A·B` — λ, μ are free labels and the
rank drop is `B = 0`, the L-value renamed; (b) ledger 516's κ(y, 0) = 0 at EVERY y, so κ is a
σ-sensitivity gauge, not a zero detector; (c) the 516 route-around is Taylor's theorem
(`c(Z) = |δ ξ′(ρ)| + O(δ²)`); (d) `finiteBank_hp_supply` is `diagOp` on the finite product's
own zero set — Retention, not Recognition. What follows is kept as the record of the
instrument and of what it measures; none of it is a proof step, and B3's sign mechanism is
the door's, which the door-class law (§2) restricts to pole swarms.

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

**B1 — THE 3D LANE PENCIL, BUILT (2026-09-01, ledger 518, `tmp/att518_lanepencil3d.py`).**
Ledger 110's queued fix, realized on the locator's own definitions: site vectors
`w·a_n·(cos θ_n, sin θ_n, h_n)` in ℝ³, lane vectors the per-lane sums, real Gram, contact
depth `det G / ∏|v_L|²`. Three height readings to run the equality test first. RESULT: the
trivial lift (`h` a common per-lane constant) touches at the zeros to 1e−7 and IS the
readout squared plus the phase-lock area term — restatement. The genuine lifts (`h = 1` or
`h = log x_n` per site) touch where the HEIGHT-NORMALIZED lanes balance,
`R_P/H_P = R_M/H_M`, not where `R_P = R_M`: the touch is displaced from the L-zero by the
lane imbalance (χ₃ first zero: mass +1.5e−2 against imbalance 1.7e−2; winding −1.4e−3
against 1.6e−3; η: −1.4e−4 and −4.6e−5), the imbalance being the log 2 clock of ledger 105.
The third coordinate is a DC 150–10,000× the transverse resultants, so both lane vectors are
nearly vertical and the dynamic range is no better than the 1D closure's. Four or more
lanes in ℝ³ are always dependent, so the real 3D Gram is identically singular past three
residue lanes. Verdict: the 3D lane pencil is a built instrument whose touch set equals the
zero set only in the trivial lift; it supplies no operator whose eigenvalue is the ordinate.
B1 is DONE. The HP object remains the Hermitian tower of `grh_of_hermitian_traceLimit`.

**B1/B2 STATE (2026-09-01, ledger 516, `tmp/att516_cellpencil.py`).** Built and run.
Identity gate: (i) PASS — cell sums reproduce the compiled channel identity B = (π/3)·L at
rel err 1.6e−10, and κ(y,0) = 0 exactly; (ii) PARTIAL — the ledger-balance check is
consistent at truncation grade (5.3e−2 against a 2.4e−2 tail at 4000 zeros), NOT the 1e−12
this file asked for; the RvM tail correction is OWED.
Result kept: cell resolution raises the drift signal **~300×** over the 2-lane scalar
(6.7e−4 → 2.13e−1 at δ = 0.05), confirming ledger 108's diagnosis with a number; κ ∝ δ²
with κ(0) = 0 EXACT, so the floor is arithmetic (δ_min ≈ 3e−9 in float64) — qualitatively
better conditioned than the Hankel census, which fails at every depth in double precision
(ledger 232).
Withdrawn: the pre-registered SNR comparison. I computed a different statistic from
ledger 110's (mine: event vs neighbouring heights; theirs: drift shift across zeros), so
the rule cannot be adjudicated by that run — the ledger-151/233 species, named in 516.
ENCOUNTERED BLOCK: κ takes δ as an input; it is a sensitivity calibration, not a zero-side
detector. Reading a zero's own drift needs its β. This is `nonempty_coupling_iff` in the
detector's coordinates.
ROUTE AROUND — STRUCK 2026-09-01 (ledger 517, equality test): the proposed "depth-vs-drift
law" for the closure depth at fixed abscissa ½ is Taylor's theorem, `c(Z) = |δ·ξ′(ρ)| + O(δ²)`.
It measures a derivative and is not on the critical path. (Record of the proposal: closure
depth `focal_closure.closure`, synthetic FE-respecting quadruple in the w = z² chart,
window-contour chart for multi-zero work — ledgers 208, 235.)

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
Constraint from ledger 517: the certification's sign mechanism, if it is the clock door's
per-clock positivity, is confined to pole swarms (`bank_convergence_bounds_floor_sum`); so the
arithmetic cannot enter B3 through clock products with prime windings under any face, carrier
scale or fiber warp. A B3 that closes must carry its sign from ends and winding jointly, not
clock by clock.

### Track E — the seating in the EQUALITY register (opened 2026-09-01, ledger 523; RETAGGED 2026-09-02, ledger 529: a READOUT REGISTER, not the space)

Suzuki's screw-function framework (arXiv:2206.03682, 2301.00421, 2606.09096; read at source)
is a chart-side readout register, NOT the house helix (the 523 identification is retracted,
ledger 529). The house Hilbert space is `CarrierThreeDMode p r = CarrierState3D p r →₀ ℂ`,
functions on carrier states indexed by height, with `carrierThreeDOperator = diagOp ordinate`
(companion §operators). Suzuki's ℓ²(Γ) helix `x(t) = ((e^{iγt}−1)/γ)_γ` is indexed by ZEROS: it
is the spectral shadow. His screw line `S_t(z)` has prime block
`Σ_{n≤e^t} Λ(n)n^{−½}(e^{−iz(t−log n)}−1)/(iz)` = the companion's bank state at height `e^t` for
the von Mangoldt fiber, each phasor replaced by its integral since birth, sharp cutoff for the
growth window, read at the spectral variable `z` and collapsed to a scalar (the collapse that
degenerates the two-lane Gram, ledger 108 / att518). Unconditional in this register:
`Ψ(t) = Σ_γ (1−cos γt)/γ²` with chordal profile `2Ψ`, the prime side the kinked ramp (ends,
winding kinks at `log n` with weight `Λ(n)/√n`, Archimedean). RH ⟺ Hilbert not Krein
(= `FoliatedPolarization`).
The leaf in this register: **RH ⟺ `‖P̂Dψ‖²_{L²(ℝ)} = π⟨ψ,ψ⟩_W` ∀ψ** (Thm 1.4), zero-free via the
explicit helix `S_t(z) = (i/2)(1+Θ_ξ^♯)P_t` — an EQUALITY, identity-discharged. RH enters its
proof at ONE place: Prop 4.1, the orthonormality in L²(ℝ) of `F_γ = √(m_γ/π)·i(1+Θ_ξ)/(2(z−γ))`,
i.e. Θ_ξ inner ⟺ `E_ξ = ξ + ξ′` HB ⟺ RH (Lagarias; house 181–184). TAG: EQUIV.
- E1 DONE 2026-09-01 (`ZetaScrewHelix.lean`, standard axioms): `screwTerm`, `zetaScrew`,
  `screwTerm_summable`, `helixVec`, `helix_chordal_term_online`,
  `helix_chordal_profile_of_online` — the zero-side helix through the origin with chordal
  profile `2 Re Ψ` under on-line zeros.
- E1b DONE 2026-09-01 (`ZetaScrewFourier.lean`, ledger 524, standard axioms):
  `zetaScrew_fourier` — `∫₀^∞ Ψ e^{izt} = −z^{−2}·ξ′/ξ(½ − iz)` for `Im z > ½`, from the compiled
  two-point resolvent trace (Suzuki Thm 1.1(1)); on the way, **`zeta_half_ne_zero`** and
  `half_not_mem_nontrivialZeros` (the centre is not a zero, via the ordered carrier series),
  `xiLogDeriv_half`, `screwTerm_laplace`.
- E1c DONE 2026-09-01 (`ZetaScrewReal.lean`, ledger 525): `conjZero`, `spectralCoord_conj`,
  `screwTerm_conjZero`, **`zetaScrew_im` (Ψ real)**, `zetaScrew_re_nonneg_of_online` (Ψ ≥ 0 under
  on-line zeros).
- E1d DONE 2026-09-01 (`ZetaScrewArithmetic.lean`, ledger 526): `logDeriv_riemannXi_arith`
  (ξ′/ξ on `Re s > 1` = ends + Archimedean clock − von Mangoldt series),
  **`zetaScrew_fourier_arith`** (Ψ̂(z) = −z⁻²[1/s + 1/(s−1) − ½ log π + ½ Γ′/Γ(s/2) − Σ Λ(n)n^{−s}],
  `s = ½ − iz`, `Im z > ½` — the transform side of the explicit formula in profile form),
  `endsProfile`/`endsProfile_laplace` (the ends' time profile `4(e^{t/2}+e^{−t/2}−2)` has
  transform `−z⁻²(1/s + 1/(s−1))`: field 1 of 3 of Suzuki Thm 1.1(2)).
- E1e DONE 2026-09-01 (`ZetaScrewRamp.lean`, ledger 527): `kink`, `windingWeight`,
  `rampTerm`, `rampProfile` (= Suzuki's `Σ_{n≤e^t} Λ(n)n^{−½}(t − log n)`); `kink_laplace`
  (`∫₀^∞ (t − log n)₊ e^{izt} = −z⁻² e^{iz log n}`), `windingWeight_mul_exp_log` (kink transform
  = `LSeries.term ↗Λ (½ − iz) n`), `rampTerm_integral_norm` (exact norm integral
  `(Im z)⁻² Λ(n) n^{−(½+Im z)}`), **`rampProfile_laplace`** (`∫₀^∞ R e^{izt} = −z⁻² LSeries ↗Λ (½ − iz)`,
  `Im z > ½`): field 2 of 3 of Thm 1.1(2).
  Not yet compiled: Thm 1.1(2) field 3 (Archimedean; needs the digamma partial-fraction series,
  absent from Mathlib — checked at source, ledger 527) and transform uniqueness giving Ψ
  pointwise; the converses (Ψ ≥ 0 ⟹ RH; screw kernel PSD ⟹ RH).
- E1f DONE 2026-09-01 (`ZetaScrewPrimeSide.lean`, ledger 528):
  `integrableOn_tsum_of_summable_integral_norm` (generic), the three integrabilities,
  `primeSideProfile = ends − winding`, `primeSideProfile_laplace`, **`archRemainder_laplace`**:
  `∫₀^∞ (Ψ − ends + winding) e^{izt} = −z⁻²[½Γ′/Γ(s/2) − ½ log π]` — the zero helix minus the
  prime side has no arithmetic content in its transform. Field 3 isolated as a statement about a
  compiled function.
- **E3 sharpened (ledger 528, source read):** `F_γ` is the normalized reproducing kernel of
  `K(Θ_ξ)` at `γ` (`Θ_ξ(γ) = −1`). Prop 4.1 = the reproducing property; RH enters once, as
  `E_ξ` HB ⟹ `Θ_ξ` inner. `Gram(F) − I` = residue contribution of UHP zeros of `E_ξ`. Real-line
  form: `⟨F_γ,F_γ′⟩ = (√(m_γ m_γ′)/π)∫ A²/((A² + A′²)(x−γ)(x−γ′)) dx`, `A(x) = ξ(½ − ix)`.
- E2: the F_γ Gram as the registration defect: `Gram(F) − I` computable from ξ on the line;
  measure it on the verified range (must be 0) and on a Davenport–Heilbronn control (must not
  be), per the design law of `weil-cell-probe-null` (control fails by MISSING structure).
- E3: the residue evaluation of `⟨F_γ, F_γ′⟩_{L²(ℝ)}`: exactly which residue a UHP zero of E_ξ
  contributes. This is where a house-native identity proof would have to act.

### Track W — the proof half of [HP-LEAF]: Weil's explicit formula for test functions,
### strip form (opened 2026-09-02, ledger 534; Sam: "go for the long hard theorem")

**Target theorem (W).** For `F : ℂ → ℂ` entire with `‖F(σ+it)‖ ≤ C/(1+|t|)³` on the strip
`−δ ≤ σ ≤ 1+δ` (`δ > 0`), with `F(s) = ∫ g(x) e^{(s−½)x} dx` for `g` smooth, supported in `[−B, B]`
(band-limited in the spectral variable: `F(½ + iτ) = ĝ(τ)`):
```
Σ'_ρ m_ρ F(ρ) = (1/2π)∫ F(1+δ+it) E(1+δ+it) dt + (1/2π)∫ F(−δ+it) E(1+δ−it) dt
                − Σ_n (Λ(n)/√n)(g(log n) + g(−log n))            [finite: n ≤ e^B]
```
`E = 1/s + 1/(s−1) − ½ log π + ½ Γ′/Γ(s/2)`. Read on the built object: `ν_Q` (532) integrates every
observable of bandwidth `≤ log Q` EXACTLY as the zero comb.  TAG: the theorem is unconditional
and classical (Weil 1952); its compiled form is what turns the measured leaf into a theorem.

**Route (chosen for reuse; no bound on ξ′/ξ at large height is ever needed).**
```
[W]  ⟸ [W5 assembly]  strip boundary of F·ξ′/ξ = 2πi Σ_ρ m_ρ F(ρ), then the two lines evaluated
     ⟸ [W4 zero side]  per zero: stripBoundary(F·(·−ρ)⁻¹) = 2πi F(ρ)   (rect residue + T→∞)
                       Σ_ρ m_ρ ∮ F·(1/(s−ρ)+1/ρ) = ∮ F·Σ_ρ m_ρ(…) = ∮ F·(ξ′/ξ − A)
                       compiled inputs: xi_logDeriv_partial_fraction (Hadamard, constant A),
                       rectangleBoundaryIntegral_holo_add_residues, rect_winding,
                       rectangleBoundaryIntegral_eq_zero_of_differentiableOn (Cauchy–Goursat),
                       Mathlib differentiableOn_dslope (removable singularity)
     ⟸ [W3 exchange]   Σ_ρ and ∫ over the lines: majorant ‖F‖·|s|/(|s−ρ||ρ|) ≤ C m_ρ/|ρ|² via
                       1/(ab) ≤ (1/a+1/b)/(a+b) and integrable_inv_one_add_sq; summability from the
                       compiled summable_xiOrderNat_div_norm_sq_nontrivialZeros; integral_tsum
     ⟸ [W2 prime side] on Re s = 1+δ: ξ′/ξ = E − Σ Λ(n)n^{−s} (logDeriv_riemannXi_arith); on
                       Re s = −δ: ξ′/ξ(s) = −ξ′/ξ(1−s) (xiLogDeriv_odd); exchange Σ_n with ∫ by
                       LSeriesSummable_vonMangoldt at 1+δ; ∫F(σ₀+it)n^{−it}dt = 2π g(log n) n^{σ₀−½}
                       by Fourier inversion (Mathlib Integrable.fourierInv_fourier_eq) — the
                       δ-dependence cancels, the sum is finite for band-limited g
     ⟸ [W1 strip contour]  lineIntegral, stripBoundary; decay ⟹ integrable lines, horizontal
                       segments → 0; rectangle → strip (intervalIntegral_tendsto_integral);
                       strip Cauchy (= 0) and strip residue (= 2πi F(ρ))   FILE 1: WeilStripContour
     ⟸ [W0 test class]  F entire from compactly supported g (differentiation under the integral,
                       the XiStageHolomorphy pattern); decay ‖F(σ+it)‖ ≤ C/(1+|t|)³ by three
                       integrations by parts, or as a hypothesis of the class with inhabitation
                       proven separately
```
Status 2026-09-02 (ledger 534 progress): **W1 BUILT** (`WeilStripContour.lean`: strip Cauchy,
strip residue). **W3/W4 BUILT** (`WeilZeroSide.lean`: `stripBoundary_mul_logDeriv_xi` —
`∮_strip F·ξ′/ξ = 2πi Σ'_ρ m_ρ F(ρ)`, decay order ≥ 4, unconditional). **W2 COMPILED**
(`WeilPrimeSide.lean`: `laplaceTest_line_fourier` — `∫F(σ+it)e^{−ity}dt = 2π g(y)e^{(σ−½)y}`;
`lseries_line_exchange`). **W5 BUILT** (`WeilExplicitFormula.lean`: `weil_explicit_formula`).
**W0 COMPILED** (`WeilTestClass.lean`: `laplaceTest_differentiable`, `laplaceTest_decay`,
**`weil_explicit_formula_smooth`** — the theorem for every smooth compactly supported `g`, no
analytic hypothesis). Decay order in [W] is 4 (not 3). **[W] COMPILED** — tag the node
COMPILED (ledger 534). CALIBRATION (retraction, same day): [W] is a compiled classical trace
identity. It does NOT discharge the proof half of [HP-LEAF] as first written: the att532 object
`ν_Q` (sharp cutoff, END term, `ϑ′/π`) is a different truncation and its relation to [W] is a
truncated explicit formula, NOT compiled. It does NOT touch [HP]: positivity of the trace on `|ĝ|²`
tests = Weil's criterion = the theorem. Under the rule-11 guard this skeleton is still a
RESTATEMENT plus one classical identity plus numerics: every compiled node is EQUIV or INSTRUMENT;
no STRONGER-and-constructive leaf exists yet. "One node away" measures nothing.

**COMPILED 2026-09-03 (ledger 563, `RequestProject/TruncatedExplicitFormula.lean`, standard
axioms): the truncated explicit formula at a growth front — the "stage measure ↔ zero comb"
relation retracted above as NOT compiled — in the cubic-taper form.**
`truncated_explicit_formula_cubic`: for `x = e^L`, `s₀` off the zero set, `a < 0 < 1 < b`,
`a < Re s₀ < b`,
```
ξ′/ξ(s₀) + Σ'_ρ m_ρ K(ρ−s₀) = (1/2π)[∫ K(b+it−s₀)E(b+it)dt + ∫ K(a+it−s₀)E(1−a−it)dt]
                               − Σ_n W(log n)·Λ(n)n^{−s₀},
K(w) = (x^{4w} − 3x^{3w} + 3x^{2w} − x^w)/(w⁴L³),   W = cubic B-spline,
```
`cubicProfile_log_eq_one`: `W = 1` exactly for `n ≤ x` (sharp front); `cubicProfile_log_eq_zero`:
`W = 0` for `n ≥ x⁴`; the zero sum converges absolutely (`K` decays at order 4). General form
`stripBoundary_pole_mul_logDeriv_xi`: any kernel continuous on the two lines with decay 4 there
and a simple residue-one pole at `s₀` inside the strip. Route: the pole handled by partial
fractions against the entire factor `G = K·w` (decay 3 on the strip), Track W's residue and
exchange lemmas reused on the lines via the line extension `s ↦ F(σ + i·Im s)`; prime side by
Fourier inversion of the explicit B-spline profile (right line) and its reflection (left line,
vanishing at `−log n`). The END term is the residue `K(1−s₀)` of the pole of `E` at `s = 1`
inside the strip — measured (att563), residue extraction NOT compiled. NOT compiled: the fully
sharp cutoff (conditionally convergent zero sum; needs `ξ′/ξ` on horizontal lines). TAG: COMPILED
identity, the bridge item 3 of ledger 557 — an INSTRUMENT-grade exact relation, EQUIV-free; it
makes the settling register of item 2 (ledger 558) a statement about the zero comb by identity.
Not the STRONGER leaf.

**COMPILED 2026-09-03 (ledger 564, `RequestProject/SelbergTruncatedFormula.lean`, standard
axioms; Sam: "why don't you build it"): the SAME identity for Selberg's linear taper `Λ_x`
(Titchmarsh 14.20) — the object att554d/560 measured.** `truncated_explicit_formula_selberg`:
`K₁(w) = (x^{2w} − x^w)/(w²L)`, weight exactly `1` for `n ≤ x` (`linProfile_log_eq_one`),
`log(x²/n)/log x` on `[x, x²]` (`linProfile_eq_taper`), `0` past `x²` (`linProfile_log_eq_zero`);
END term `K₁(1−s₀) = (x^{2(1−s₀)} − x^{1−s₀})/((1−s₀)²L)`, the form in `end-term-dc-law`. The two
costs named at 563 were built: `summable_logWeight_nontrivialZeros`
(`Σ_ρ m_ρ (1 + log(1+|ρ|))/|ρ|² < ∞`, dyadic shells on the compiled count
`xi_weighted_zero_count_disk_bound`, index `Nat.log 2 ⌊‖ρ‖⌋₊`, `Finset.sum_fiberwise_of_maps_to`)
and `integral_inv_mul_inv_le` (`∫dt/((1+|t|)(1+|t−γ|)) ≤ 12(1 + log(1+|γ|))/(1+|γ|)`, three
regions, `∫_{−R}^{R}(1+|t|)⁻¹ = 2 log(1+R)`); plus `stripBoundary_div_sub_eq₁`, the strip residue
at decay order 1 (the entire factor `G₁ = K₁·w` decays only at order 1). Measured att564 at
x = 60 and x = 20 (see ledger 564): identity to the truncation level of the order-2 kernel.

**COMPILED 2026-09-03 (ledger 565, `RequestProject/TruncatedFormulaEnds.lean`, standard axioms;
Sam: "make progress"): the two END terms as residues, and the CLASSICAL FORM.**
`stripBoundary_kernel_mul_ends`: `∮ K·E₀ = 2πi[E₀(s₀) + K(0) + K(1)]` for `E₀ = 1/s + 1/(s−1) − ½log π`
(the two ends of the helix, poles at 1 and 0). `selberg_identity_classical` /
`cubic_identity_classical` (Re s₀ > 0, ζ(s₀) ≠ 0):
```
Σ_n Λ_x(n)Λ(n)n^{−s₀} = −ζ′/ζ(s₀) + K(1−s₀) + K(−s₀) − Σ′_ρ m_ρ K(ρ−s₀) + R_clock(s₀),
R_clock(s₀) = (1/2π)[∫ K(b+it−s₀)Ψ(b+it)dt + ∫ K(a+it−s₀)Ψ(1−a−it)dt] − Ψ(s₀),  Ψ = ½Γ′/Γ(s/2).
```
The END DC `K(1−s₀)` and the anti-end `K(−s₀)` are compiled residues; `R_clock` is the trivial
zeros `−Σ_{k≥0}K(−2k−s₀)` (measured att565 to 1e−5), NOT compiled as a residue sum: its gate is
the digamma partial fraction, absent from Mathlib (ledger 527, same gate as Suzuki field 3). TAG:
COMPILED identity, the END-term law of `end-term-dc-law` now in Lean for both ends.

### Track P — RETIRED same day (Sam, 2026-09-02: "i don't know why you brought the weil form in,
### it doesn't belong"). Kept for the record only; not a slot in the HP plan.
### (was: the Weil form on the prime phasor bank, ledger 537)

**Object.** `weilForm g = Σ'_ρ m_ρ F_g(ρ) conj F_g(1−conj ρ)` (= `Σ_ρ m_ρ |ĝ(τ_ρ)|²` on the line),
expressed on the bank by the compiled explicit formula applied to `G = g ⋆ g̃` (`weilForm_eq`,
`WeilPhasorBank.lean`). Toeplitz form with symbol = zero comb; prime phasors = the symbol's Fourier
coefficients at `±log n`; Archimedean part = continuous part.
**Target.** `[P] weilForm g ≥ 0 ∀ g` = Weil's criterion = [HP] (EQUIV — this is the theorem, not a
step toward it). **Provable rungs**: `[P_L]` positivity for `supp g ⊆ [−L, L]`:
  `[P_{L<(log 2)/2}]` Archimedean only (Yoshida 1992) — needs the shift of the Archimedean line
  integrals to the critical line (end residues `F_G(0), F_G(1)`) and the positivity of the resulting
  kernel: NOT compiled; `[P_{L<(log 3)/2}]` one prime (p = 2 and its powers): finite check against the
  Archimedean form; each further prime one rung. Every rung is finite information about all zeros
  (the zeta-23 class); no finite L is [HP]. The STRONGER-constructive leaf, if one exists, is a
  spectral factorisation of the symbol (`k = φ ⋆ φ̃`), which exists iff the symbol is positive:
  exhibiting φ from primes is the only non-restatement target on this track.
Status 2026-09-02: **P1 COMPILED** (`WeilPhasorBank.lean`: `weilForm`, `weilForm_eq`,
`laplaceTest_convolution`, `laplaceTest_conjReflect`; standard axioms). **att537b**: the compiled
identity is numerically exact on the bank (prime side = zero side to 1e−4…1e−9 for L = 0.3…3.5,
after a control bug — half the zero set — was found and fixed); Gram form positive with λ_min
5.1e−3 → 1.7e−6 as 1 → 210 prime powers enter. Next rung `[P_{L<(log 2)/2}]`: shift the
Archimedean line integrals to the critical line and prove the resulting kernel positive on small
supports (Yoshida) — NOT compiled.

### Track S — the seat at prime-computable anchors (opened 2026-09-02, ledgers 541–546;
### Sam: "go after the seat, make adjustments if you need to")

**Adjustment.** The seat in registration coordinates (541): the window Hankel is clock Hankel (PD)
+ S-Hankel (indefinite alone); the event-registering warp maps Gram points to zeros with
displacement (π/ϑ′)(1 − S(γ⁺)); "the defect is corrected by the warp" = pushforward of the clock
measure by a real map. Relocated seat (542–543): the FE-paired form `A_n(s) = Σ m_ρ (s−ρ)^{−(j+1)}
(s̄−1+ρ)^{−(k+1)}` at anchors `Re s > 1` — jet-computable, hence prime-computable (absolutely
convergent) — is nonnegative at every anchor and order iff RH. ⟹ COMPILED
(`primeAnchorForm_re_nonneg_of_online`). ⟸ COMPILED UNDER ONE HYPOTHESIS
(`exists_primeAnchorForm_neg_of_leader`, `StrictLeader ρ σ₀`): a strict off-line leader at its
own anchor forces a negative form. STRUCTURAL FACT COMPILED: on-line zeros never lead at an
off-line anchor (`feDist_online_ge`, `D₀_lt_sq`).
**The gap, closed to one attainment hypothesis (547).** No oscillation argument is needed: with
the correct test root the pair term is negative at EVERY order (att547; my earlier "oscillation"
came from a sign error in my own script, caught by a planted sanity check). COMPILED:
`strictLeader_of_maxDepth` (a deepest zero strictly leads at its own anchor),
`exists_primeAnchorForm_neg_of_maxDepth`, and **`rh_of_primeAnchorForm_nonneg`**: if the depth
supremum is attained, nonnegativity of the order-N prime-anchor form at every `1 < σ₀ < 3/2`
implies RH. The 547 gap `∃ ρ, MaxDepth ρ` is **CLOSED (548, 2026-09-02)**: widen the test
family to every polynomial `R` with `R(0) = 0` (the full Hermitian form `A_n(s) ⪰ 0 ∀ n`). At the
anchor over ANY off-line zero, `R_N = y^N · Π_{near ρ' ∉ pair}(y − x′_{ρ'}) · (y − μ)` annihilates
every other near zero exactly (FE partners included), far zeros have node product ≤ 1 < ab, and
one complex root `μ` makes the pair term `≤ −c (ab)^N`: no extremal depth, no leader, no
oscillation. COMPILED (`SeatPrimeAnchorHermitian.lean`, standard axioms):
`hermForm_re_nonneg_of_online`, `exists_hermForm_neg`, **`rh_iff_hermForm_nonneg`** —
unconditional in both directions. att548: pre-registered P1–P6 all confirmed (old family NOT
eventually negative with a deeper zero 0.15 off the anchor ordinate; new family negative for all
N ≥ 4; q = 0 control ≥ 0; planted-bug control fires). `[S]` tag: EQUIV (rigidity), now with no
hypothesis on either side; n = 1 positivity at Re s > 1 is a theorem (exterior). The node is
FILLED in the 1D READOUT register only. **CORRECTION (Sam, same day): "this is only workable in
1D, not on the 3D helix."** The annihilator's roots sit at the chart nodes of the other zeros — a
zero-side certificate with no carrier counterpart; the fiber exposes phasors, not zero locations.
Retag: `[S]` = EQUIV, 1D readout; NOT a template for the STRONGER leaf. The only 3D-readable part
is the object itself: `v*A_n(s)v` is a quadratic form in the bank jets `Σ Λ(n) n^{−s}(log n)^j` at
one fully-grown height; its positivity from the bank's geometry is the seat, untouched here.
Files: `RequestProject/SeatPrimeAnchor.lean`, `RequestProject/SeatPrimeAnchorHermitian.lean`;
`tmp/att541_warp_pitch_S.py`, `tmp/att542_seat_prime_anchor.py`,
`tmp/att543_seat_prime_anchor_dominance.py`, `tmp/att548_annihilator_repair.py` (+ results).

### Track N — no-origination in the cascade register (2026-09-02, ledgers 550–553; independent audit)

The compiled DPI theorems are, by type, `offline_zero_violates_dpi` (a tautology whose hypothesis
`hHP` is "every genuine zero has a source") and `limit_dominance` (Hurwitz: every limit zero has
stage-zero ancestry, conclusion `F n z = 0`). Neither reaches N_off. The audit's requested
strengthening is COMPILED at its true strength (`SourceLabelledCascade.lean`):
`SourceLabelled C := ∀ n z, stage n z = 0 → z.im = 0` ⟹ `Complete C` ⟹
**`projection_cannot_originate_events`** ⟹ **`rh_of_sourceLabelled_cascade`**. Where the
hypothesis lives, compiled: **`twoPhasorStage_vanishes_off_fold`** — the first phasor-built stage
`1 − 2^{−(½+iz)}` vanishes at `z = i/2` (the helix end), so carrier-phasor stages are never
source-labelled; source labelling = real-rootedness of the approximants, which exists exactly under
RH (Pólya; the Hadamard partial products, labelled by the zeros). `[N]` tag: EQUIV, one node —
"exhibit a real-rooted cascade converging to ξ from the constitution alone." The five-line
derivation of N_off ≡ 0 from the fiber equivalence (550) fails at step 2 (value vs state) and
consumes no Euler-product fact. Ledger 551–552: the F6-consuming step in object-native form is
"the prime clocks' phasor sum settles at every height right of balance" (EQUIV via Landau); four
house-frame angles run, no third form found.

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
- Track B is an instrument track (ledger 517): B1–B2 calibrate σ-sensitivity and nothing
  else; B3 is where the arithmetic must enter and where every prior route in the ledger
  terminated. The compiled door slot `riemannHypothesis_of_bank_convergence` is EQUIV:
  `BankDoorClassLaw` shows it admits only pole swarms. The STRONGER-constructive leaf the
  guard demands is still not in hand. Its required shape is now sharper: a sign mechanism
  that survives the limit WITHOUT a per-clock DC — ends and winding consumed together. If B3
  terminates the same way, the entry says so at exactly that strength, with the encountered
  block named, and the plan is refined here — not softened, not inflated.
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
`BankHerglotzReduction`, `BankDoorClassLaw` (the door's admissible class: `clockFloor`,
`bank_logDeriv_re_le`, `bank_convergence_bounds_floor_sum`,
`bank_convergence_card_bounded_of_winding_ge`), `ClockPoissonBarycenter`
(`symClock_logDeriv_face_form`, `unitaryClocks_poisson_barycenter_right/left`,
`..._eulerFace/_antiEulerFace`), `ClockSmallWinding` (`symClock_logDeriv_small_winding`),
`PrimeClockDoor`, `DVPChannelBase`, `SeatingLadderFold`.
Registration: `ZetaContourArgument`, `CarrierLedgerBalance`, `PencilCellEdgeDoor`,
`XiZeroLedgerResolvent3D`, `SpectralCarrierKernelCoupling3D`, `ZetaContourCouplingDefect3D`,
`ZetaContourGlobalIdentification3D`, `SeatingLedger`, `SeatingHalfFlips`, `SeatingFloor`,
`SeatingOddFlips`, `DVPOffLineIff`.
Operator/space: `CarrierUnboundedResolvent3D`, `FoliatedPolarization`,
`FoliatedGlobalPolarization`, `FoliatedDeterminant`, `HilbertPolyaResolventTrace`,
`ZetaScrewHelix` (`zetaScrew`, `helixVec`, `helix_chordal_profile_of_online` — the zero-side
helix, Suzuki dictionary), `ZetaScrewFourier` (`zetaScrew_fourier`, `zeta_half_ne_zero`,
`half_not_mem_nontrivialZeros`, `xiLogDeriv_half`, `screwTerm_laplace`), `ZetaScrewReal`
(`conjZero`, `zetaScrew_im`, `zetaScrew_re_nonneg_of_online`), `ZetaScrewArithmetic`
(`logDeriv_riemannXi_arith`, `zetaScrew_fourier_arith`, `endsProfile_laplace`), `ZetaScrewRamp`
(`kink_laplace`, `windingWeight_mul_exp_log`, `rampTerm_integral_norm`, `rampProfile_laplace`),
`ZetaScrewPrimeSide` (`integrableOn_tsum_of_summable_integral_norm`, `primeSideProfile_laplace`,
`archRemainder_laplace`), `HPHelixSupply`,
`HelixWarpCovariance`.
Banks: `FiniteBankMass`, `BankNoTransient`, `PrimeClockCentered`, `PrimeClockOrdering`,
`PrimeClockData`, `EtaLogDerivBank`, `CarrierChannelReadout`, `CarrierTransientRigidity`,
`CarrierCarlsonMean`, `DVPCarrierContinuation` (`etaLim_eq_zeta`).
Seat: `SeatScalarCriterion` (`seat_criterion_iff`, `depth_criterion_iff`,
`seat_energy_ge_window`), `DVPSeatRungOne`, `DVPSeatResonance`, `SeatingMassDisk`,
`SeatingMassLedger`, `SeatingMassPositivity`, `SeatingMassWrap`, `DVPSeatRealPart`,
`XiStructureHBSeat`, `XiStructureNativeSeat`.
Stages: `XiTailStripBound` (`xiStage_tendsto_xiIntegral`, `xiStage_extent_hasDerivAt`),
`XiStageHolomorphy` (`xiStage_hasDerivAt`, `xiStage_tendstoLocallyUniformly`,
`xiIntegral_differentiable`, `deriv_xiStage_tendsto`), `SeatMassEtaForm`
(`logDeriv_riemannXi_splice`, `seatMass_eta_form`, `riemannHypothesis_of_eta_mass`),
`SeatingDeepPairBound`.
Numerics: `focal_closure.py` (Family/lane machinery), `tmp/att110_detector.txt` (2-lane
baseline), `tmp/att518_lanepencil3d.py` (the 3D lane pencil, three height readings), `tmp/att185b_grampencil.txt`, `tmp/att187_decomposition.txt`,
`tmp/att224`–`att233` (census controls), `tmp/att184c_confirm.txt` (m(z) field).

Papers: `automorph/hp_pencil.tex` (Theorems inertia/census/Stieltjes, the operator
reading, the seat split), `automorph/grh_companion.tex` (the three operator levels,
`grh_of_selfAdjoint_resolvent_capture`, `rh_iff_symmetrizedLineTower_traceLimit`),
`automorph/universal.tex` (Part I, §carrier-S, the meta method).

**Sam's first-collision frame (2026-09-03, ledgers 569–570).** RH ⟺ no real double zero of
H_t = e^{−t∂²}ξ(½+i·) on [0, t₀]. Exact at a zero: H′_t(x) = −θ′_t(x)·S_t(x) with the odd lane
S_t = (1/x)∫(−Φ_t′)(1 − cos xu) > 0 (positive identity, t ≤ 9.36) and the one-ended bank zero-free in
the closed UHP (theorems, elementary, not compiled). CONTROL: t < 0 kernels are positive, even and
decreasing and DO collide — positivity + J cannot decide; the arithmetic must be transported along the
flow at the bank level. REGISTERED: ẋ_k(0) = 2i·FP(ρ_k) = the prime side of the compiled Riesz formula
at s₀ → ρ_k (verified 2e−4); closing rates 8 − screening exact; 54% of gaps close forward
(crystallization pair by pair). Slot: STRONGER-constructive candidate = a per-pair barrier from the
registered closing rates; not yet a proof plan.

## SIMPLICITY SKELETON (2026-09-03, ledgers 569–577), written backward from the target

**Target S.** Every on-line zero ½+iγ of ζ is simple ⟺ Z′(γ) ≠ 0 at every zero of Hardy's Z
[EQUIV, Zeta23 `hasDerivAt_hardyZ`, `deriv_hardyZ_eq_zero_iff`]. Off-line zeros are invisible to Z
and belong to Target R (RH) below.

- **S1 [COMPILED 574]** For every front N ≥ 1, t ≠ 0:
  Z′(t) = Re[i e(t)(ϑ′(t)·bank_N − clock_N)] + Re[i e(t)(ϑ′·tail_N + tail′_N)], with
  |tail_N|, |tail′_N| ≤ explicit(N, t) → 0 (`tail_bound`, `tailDeriv_bound`).
  Hence Z′(γ) = lim_N Re[i e(γ)(ϑ′(γ)·bank_N(½+iγ) − clock_N(½+iγ))].
- **S2 [COMPILED 573]** clock_N = Σ_{d≤N} Λ(d) d^{−s} bank_{N/d} = −bank′_N (multiplicativity; the
  property every t ≠ 0 lacks, 572 control).
- **S3 [OPEN — the only open node for Target S]** At a crossing (Z(γ) = 0), the limit in S1 is ≠ 0:
  the clock-sampled growth history never equals ϑ′ × endpoint up to the vanishing tails.
  Would suffice (targets, not claims):
  (a) a many-phasor two-clock criterion generalizing 577 (double zero ⟺ finitely many exact
      quarter-turn resonances in the rates), then `prime_clocks_incommensurable`. Holds for 2 phasors
      [COMPILED 577]; for ≥ 3 phasors the double-zero locus on the rate torus is a continuum of
      codimension 2, so the criterion must use the specific amplitudes n^{−½} and ϑ-tied phases —
      NOT formulated. Spec: compute the double-zero locus of the N = 3 zeta-rate model.
  (b) the registry route: `shadowing_implies_online_simple` [COMPILED, conditional] + the residual
      tail law (566) [OPEN, RH-strength: it also yields on-line-ness].
  (c) a Chebyshev/total-positivity inequality between clock_N and ϑ′·bank_N at crossings — no
      candidate identity; the measured ratio takes both signs and both sides of 1 (572).
  Unconditional partial: ≥ ½ − ε of zeros in [T, 2T] simple on-line [COMPILED `seating_simple_floor`
  via Zeta23]; ≥ ¾ − ε distinct [Zeta23].

**Target R (RH via Newman).** No real double zero of H_t = e^{−t∂²}ξ on [0, 0.22] ⟹ RH + S
[EQUIV, pencil; de Bruijn–Newman machinery NOT in Lean anywhere in the workspace].
- **R1 [MEASURED 570–572, not theorems]** velocity field ẋ_k(0) = registered prime field; closing
  rates 8 − screening; g² concave; Burgers boundary law dv/dt = −Im q_xx − 2v Re q_x + (Im q_x)²/v;
  control double zero at t = −0.0961.
- **R2 [OPEN]** a per-pair barrier: v(t)² > 0 on [0, 0.22] from the boundary law — needs the
  indefinite terms controlled; no candidate.
- **R3 [OPEN]** bank-level transport (571): weights e^{t log²(N/n)}; n = 1 dominance at large
  height (Polymath's mechanism) not compiled here.

**Guard (rule 11):** every leaf is EQUIV or STRONGER-and-not-yet-constructive. No leaf is discharged
by identity. This skeleton is a map, not yet a proof plan; the session's output is the location of
the single open node S3 with every other node compiled.

**STRONGER-constructive leaf (ledger 580, Sam's frame "no complex zeros supported").** Exhibit a
source-labelled cascade converging to the ξ-section (every stage entire, all stage zeros at real
heights, locally uniform convergence); `rh_of_sourceLabelled_cascade` [COMPILED] finishes. Not
filled: phasor-built stages fail labelling [COMPILED counterexample]; Hadamard partial products and
the Newman family H_t (t ∈ (0, ½)) are labelled iff RH; a cascade labelled BY ARITHMETIC is the
object to build. This is the only leaf of the skeleton that is discharged by identity (Hurwitz) once
the object exists.

**S3, density register, COMPILED form (ledger 584, `RieszMultiplicityReadout.lean`):**
m_{ρ₀}·L/2 = (prime side at ρ₀, Riesz front) − xiFinitePart ρ₀ − Σ_{ρ≠ρ₀} m_ρ K_R(ρ−ρ₀), exact at every
front. Simplicity of ρ₀ ⟺ lim_L (2/L)·(prime side − finite part − comb) = 1. Open content unchanged:
the prime side's dip at a zero is bounded below (a sup over zeros); measured 1.00 ± 0.01 at 13 zeros.

**Track S prime side (ledgers 589–592).** The door `rh_iff_hermForm_nonneg` [COMPILED] has hypothesis
Re Q_w(R) ≥ 0 with Q the zero-side form. Its prime side (589, pencil, verified 1e−4): Q_w(r) =
−2Re Σ_i f_{−i}(r)(ξ′/ξ)^{(i−1)}(w)/(i−1)!, f_{−i} explicit sesquilinear; the jets are COMPILED
(592, `hadamard_jet`), and the finite partial-fraction identity is COMPILED (594,
`HermFormJets.lean`): **`hermForm_eq_jets`** — hermForm w R = Σ_{j,k} conj(r_j) r_k · jetValue s c j k,
jetValue a finite functional of 2Re(ξ′/ξ)(s) and the jets (ξ′/ξ)^{(m)} at s = ½+iw and at the mirror
c = 1−s̄ (593 on the path: the paired first-order term is FP(s) − FP(1−s̄) = 2Re FP(s)). Door restated
**`rh_iff_jets_nonneg`** [COMPILED both ways]: RH ⟺ ∀ γ, 1<σ₀<3/2, R(0)=0:
Re Σ conj(r_j) r_k jetValue(σ₀+iγ, 1−σ₀+iγ) ≥ 0 — hypothesis side has NO zero sum. Fold COMPILED (595,
`HermFormJetsFold.lean`: `iteratedDeriv_conj_comm`, `jet_reflect`, `jet_mirror` ⟹ `rh_iff_jets_s_nonneg`,
jets at ONE point). Prime chart COMPILED (595, `XiJetsArithmetic.lean`: `xi_jet_arith` ⟹
**`rh_iff_prime_jets_nonneg`** [COMPILED both ways]): RH ⟺ ∀ γ, 1<σ₀<3/2, R(0)=0:
Re Σ conj(r_j) r_k · jetValueP(σ₀+iγ, 2σ₀−1) ≥ 0, jetValueP built from 1/s, 1/(s−1), log π, the jets of
½Γ′/Γ(·/2), and Σ Λ(n)(log n)^m n^{−s}. **No zero of ζ in the hypothesis.** Remaining on the dependency
path: closed form of `pf` (hockey stick) making jetValueP a Hankel-type form; DC = Pascal–Hankel pole/Γ
part (589, ≻ 0), AC = prime series; then the open node in its zero-free form: the sign of that form.
Content of the door's hypothesis (590–591): the positivity is carried by the actual phases γ·log p,
enslaved to the zeros; free phases violate at every degree ≥ 2. Open node unchanged in content.
