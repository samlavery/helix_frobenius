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
      Four compiled registers of the SAME node (do not count them as four problems):
        count   N_off ≡ 0                offLineMassLog_iff_offLine_zero        ledger 424, 426
        trace   windowed exhaustion      traceLimit_of_rh (converse compiled)   companion
        mass    seatMass ≥ 0 on channel  channel_mass_iff_online                SeatingMassPositivity
        intertwining  Semiconj zeroHeightCorrespondence ledgerOp carrierOp
                ⟺ every zero on the line   semiconj_iff_nontrivialZeros_online   ledger 597
                the zero-built map's defect is the drift −i(Re ρ − ½) (597, 598); the map that
                carries the fiber is the REGISTRATION: `StationRegistration t` (stations from the
                primes, zeros shadowed within half the local gap) ⟹ full intertwining ⟹ RH
                (599 — RETRACTED 603: `StationRegistration` is uninhabited, an all-sign enumeration
                against a one-sided station sequence, `stationRegistration_not_nonempty`; use 600 or
                the parallel session's `PositiveStationRegistration`).
                Count form (600, `OnePerGap.lean`): `OnePerGap t` — one zero with
                multiplicity per station gap on the compiled strip census — ⟹ every zero on the
                line AND simple (`online_simple_of_onePerGap`) ⟹ RH ⟹ full intertwining
                (`semiconj_of_onePerGap`). STATIONS BUILT (601, `RegistrationStations.lean`,
                `PrimeStrain.lean`): `primeStation X n` = first crossing above 10 of level n − 3/2 by
                ϑ/π + Ŝ_X, Ŝ_X the prime-forced strain −(1/π)Σ_{n≤X} Λ(n) sin(t log n)/(√n log n);
                `primeStation_spec` = the station equation exactly; `resid_station`:
                R(t_n) = N(t_n) − n + ½ exactly. DOOR `nontrivialZeros_online_of_primeResid`:
                RH ⟸ start n₀ ∧ primeStation X n₀ ≤ 58 ∧ ∀ n ≥ n₀, |R(t_n) − R(t_{n₀})| < 1.
                603: with a FIXED cutoff X this hypothesis is FALSE (it would bound S, and S is
                unbounded) — the door is empty. The station machinery stands for any continuous
                strain; re-instantiate it on a HEIGHT-MATCHED, Riesz-tapered strain (owed). The 58
                obligation is removed by `primeStation_le_58_of_level_le` (IVT, parallel session);
                the one-step form `onePerGap_of_adjacent_resid` replaces the run-from-n₀ form.
                OPEN NODE, exact: the adjacent residual law on the height-matched object (measured
                max 0.31–0.38 spacings over 41k zeros). HEIGHT-MATCHED DOOR COMPILED (604,
                `RegistrationSeq.lean`): `StrainSeq` (one bank per station), `seqStation`,
                `onePerGap_of_seqResid`, `nontrivialZeros_online_of_primeSeqResid`, inhabitant under
                RH stated (Ŝ_n ≡ n − 3/2 − ϑ(γ_n)/π puts every station on its zero); DC per station
                `seqResid_station_abs_le` with constant 24 + |A′| + B_n. Draft A's `fail` = the
                adjacent estimate for the prime banks. Drafts B/C/D (605): B's Laplace brick
                `laplace_pow` (`LaplacePower.lean`) puts the pole DC in the ℓ-variable of the symbol;
                C hits the oscillatory cross terms (`JKernelPhaseSign`); D with station spectra has
                its correction holomorphic iff RH (606: `stripTraceLimit_iff_GRH`; the attack is to
                spend E). Four attacks, each with its own tools.
                THE REGISTRY'S MECHANISM COMPILED (607–608, `RegistrationDensity.lean`,
                `RieszStrainDeriv.lean`, `RegistrationGapCount.lean`): `density_on_line` — on the
                line the Fejér-smoothed zero density = clockRate + Riesz prime bank + explicit
                remainders, NO ξ′/ξ term (its real part vanishes there); `rieszStrain_hasDerivAt`
                (the Riesz strain is the bank's antiderivative); **`smoothed_gap_count`**: over a
                station gap of the Riesz-strained clock the smoothed count is EXACTLY one plus the
                integrated remainders — the registration operator is designed so; "there is no
                residual" at the smoothed level. Sharp − smoothed = the Fejér boundary term alone.
                Owed: `hrem` (continuity of the clock line integrals in t). BOUNDARY TERM
                COMPILED (609, `RegistrationBoundary.lean`): smoothed count = Σ'_ρ m_ρ·gapWeight
                (exchange via uniform O(‖ρ‖⁻²) kernel bound), `gap_count_decomposition`:
                sharp count = 1 + ∫rem/π + Σ'_ρ m_ρ(1_gap − w_ρ). One-per-gap ⟺
                |∫rem/π + boundary| < ½ on every gap; on-line w_ρ = Fejér mass of the gap (≥ 0
                compiled; ≤ 1 needs ∫(1−cos Lu)/(Lu²) = π, owed). 610 (`FejerMass.lean`,
                `RegistrationWeightBound.lean`, `RegistrationRemainderIntegrable.lean`,
                `FejerTail.lean`): ∫_ℝ fejer = π COMPILED (Fourier inversion of the triangle);
                on-line w_ρ ∈ [0,1]; `hrem` DISCHARGED (`gap_count_decomposition'` needs only hB, hn);
                weights in zero–station distances: inside 1 − w ≤ (2/πL)(1/(γ−a) + 1/(b−γ)),
                outside w ≤ (2/πL)/dist and ≤ (2(b−a)/πL)/dist². EXACT RESIDUAL FORM: boundary
                term additive ⟹ B_n = Φ(t_{n+1}) − Φ(t_n), Φ := N − N_L the registration potential;
                OnePerGap ⟺ Φ(t_n) + R_n constant at the stations (R_n = archimedean drift).
                611 (`RegistrationMaster.lean`, `RegistrationWarp.lean`): MASTER IDENTITY with no
                stations, `count_identity`: N(a,b] = Δϑ/π + ΔŜ_L + ∫rem/π + boundaryTerm for all
                L > 0, 0 < a ≤ b; `S_identity` = Selberg's formula for S with Riesz weights, exact.
                Stations for ANY clock tending to infinity (`nontrivialZeros_online_of_resid'`).
                Height-matched bank `warpStrain Lf t = Ŝ_{Lf t}(t)` continuous (joint continuity
                of Ŝ in (L,t)), clock → ∞ when e^{Lf} ≤ t/20; `warp_gap_count` EXACT: count = 1 +
                ∫rem/π + B_{L_a} − (bank change), bank change ≤ (1/π)((L′−L)/L)(e^{L′}+1).
                612 (`RegistrationScale.lean`, `RegistrationFlux.lean`): THE CONCRETE REGISTRY
                `registryStrain c = Ŝ_{c log t}(t)`, c ∈ (0,1), explicit threshold 20^{1/(1−c)};
                `registry_gap_count` exact; `registry_bankChange_le` ≤ (1/π)(log(b/a)/log a)(b^c+1);
                door `nontrivialZeros_online_of_registryResid`. FLUX CONSERVATION `boundaryTerm_add`;
                `run_count`: over k gaps N = k + ∫rem/π + B(run) — net defect = END effect;
                `boundaryTerm_split` near/far; `far_weights_le` ≤ (2(b−a)/πL)·(far second moment)
                for on-line far zeros. Lattice configuration ⟹ B ≡ 0 (translation symmetry): B is
                the local irregularity. **613 CALIBRATION: the gap doors 600–612 put the gap
                boundaries at the PREDICTED-ZERO level n − 3/2; their residual law demands
                one-sided offsets, contradicted by the measured registry (signed e, RMS 0.063).
                Hypotheses uninhabited at that level. Repair = integer level (shifted strain
                Ŝ − ½ = mid-gap stations = the shadowing frame of 161), zero new mathematics.
                Even repaired, one-per-cell for ALL n is stronger than RH and expected to fail at
                close pairs (162); the honest target is the DENSITY version + the close-pair
                object (165). Direction since 607: lateral (instrument), not forward.**
                NEXT: compile the integer-level door; retag 600–612; density version.
                DC UNCONDITIONAL (602, `RegistrationDC.lean`): `resid_station_abs_le`
                |R(t_n)| ≤ C(log(t_n+1)+1) at every station; `net_defect_le`: registration bijective
                on average, net defect O(log t_M) over any run of stations. AC = the pointwise law
                |R(t_n) − R(t_{n₀})| < 1: the one open inequality, the count of one gap from primes.
      SEAT DOOR, DEGREE-N RUNGS (617–618): Q_N(s) = Σ_ρ[(s−ρ)(ρ−1+s̄)]^{−N}, 1 < σ₀ < 3/2; the
                de la Vallée Poussin (3,4,1) square goes through on the prime side at EVERY degree
                (Q_N = DC_N − 2Σ Λ(n)n^{−σ₀}cos(γ log n)A_N(log n), A_N > 0); the archimedean scaling
                (pole η^{−N} vs Γ log γ) would give 1 − β ≫ (log γ)^{−1/N}; the argument fails at
                exactly one step — off-line zero terms are sign-indefinite for N ≥ 2 (phase Nφ),
                so clusters of bad zeros within ~η of the anchor (Jensen allows ~η log γ of them)
                can cancel. SURVIVING DICHOTOMY: isolated bad zeros satisfy 1 − β ≫ (log γ)^{−1/2};
                bad zeros must cluster (Turán/Pintz-type; source-read owed). LEAF (STRONGER,
                constructive): cluster control at scale (log γ)^{−1/2}, or an anchor scheme
                restoring termwise positivity at N ≥ 2.
      DRAFTS RE-REVIEW 620: Leaf A ⟺ N_off ≡ 0 (compiled pointwise), balance = census partition
                (`balance_is_partition`, `registrationDefect_eq_resid_sub`); Leaf B2 ⟹ no isolated
                off-line zero with 1 − β < c(log γ)^{−1/2} (derived) — Turán-scale, not finite;
                Leaf C ⟺ RH on the region; Leaf D ⟺ GRH(χ) with the zero set as inhabitant.
      [HP-LEAF] AT DEGREE N — THE TOEPLITZ (CAYLEY) REGISTER (622, `SeatToeplitzRegister.lean`,
                `tmp/att622b`): w_ρ = (ρ−c)/(s−ρ) maps the line to the unit circle and nothing else
                (`transport_norm_eq_one_iff`); the degree-N seat form = Toeplitz form of
                μ_s = Σ x x′ δ_{w_ρ}; μ̂_0 = seatMass, μ̂_n = binomial combination of the jets S_2..S_{n+1}
                (`transport_pow_identity`, `toeplitzCoeff`); linear in the jets ⟹ T = T^E + T^M + T^A.
                MEASURED: T ⪰ 0 with tiny minimum (transported measure ≈ point mass at w=1 near the
                line; angular spread ≈ 2(½−σ)/spacing), T^E negative scalar, T^M negative-definite
                (ticks inside the disc), T^A positive-definite. [HP-LEAF] at degree N:
                T^A ⪰ −(T^E + T^M). TAG: the leaf; identity route = show μ_s is a positive measure
                from the faces' constitution.
      CONSTITUTION OF THE ORDERED FACE (623, `SeatToeplitzReflection.lean`, att623): two exact
                readings, T^A = T^ξ − T^E + Σ_q T^{cond_q}(s) = U·I + D − T^{P_Q}(1−s) (reflection law
                `toeplitzCoeff_reflect`). POSITIVE FROM CONSTITUTION: the unitary clock is a cotangent
                (`symClock_logDeriv_eq_cot`) = pure symmetric partial fractions over LINE zeros ⟹ its
                transported measure is positive atoms on the circle; Poisson barycenter (520) averages
                them; on the channel cond_q = barycenter − ℓ/2 ⟹ T^{cond_q} ⪰ (log q/|d|)·I at every
                degree (measured, all cases); right of the line Euler_p = barycenter − ℓ/2 with the
                uniform SUBTRACTED ⟹ not PSD (prediction refuted, C3). −T^E = |mass_E|·I + dipoles.
                THE LEAF: T^ξ ⪰ 0 ⟺ T^{P_Q}(1−s) ⪯ U·I + D — the reflected Q-free Euler side's
                transported measure dominated by the Γ-and-clock uniform background. Owed: symmetric
                partial fractions at all jet orders (Mathlib cot_series_rep), Gram positivity,
                derivative under the circle average, `condClock_toeplitz_psd`.
      CONDUCTION-CLOCK TOEPLITZ POSITIVITY COMPILED (624, `UnitaryClockJets.lean`,
                `UnitaryClockToeplitz.lean`, `ConductionClockToeplitz.lean`, standard axioms): the
                unitary clock's jets are the symmetric sums over its line zeros (`clockS_jet`), its
                mass Σ 1/|s − tick_n|² (`clockS_re_logDeriv`); its Toeplitz coefficients are
                Σ_n ω_n w_n^k with |w_n| = 1 (`clock_toeplitzCoeff`) and the Gram identity gives
                `unitaryClock_toeplitz_psd` at every degree. The conduction clock is −G_r − ℓ/2 with
                G_β = (ℓ/2)h(βv) holomorphic in β (`condClock_logDeriv_eq`); Mathlib's Poisson
                integral formula gives T(G_r) = ∮ P_r T(G_β) (`toeplitzForm_jets_rad_eq`), hence
                `conductionClock_toeplitz_lower_bound`: T^{cond_q} ⪰ (log q/(1−2σ))·I, every degree.
                In the constitution, Σ_q T^{cond_q} ⪰ 0 is now COMPILED; owed: −T^E (Γ face; atoms are
                the trivial zeros, off the circle, so not Gram-type); T^ξ ⪰ 0 is the leaf.
      THE Γ FACE, EXACT (625, att625/625b; not compiled — needs digamma partial fractions): −T^E =
                [log(t/2π)/(1−2σ)]·I + a SKEW charge M = i/(2t) + O(1/t²) at the antipode w = −1
                (closed form, telescoped digammas, = direct sum to 1e−42; the half-density ends arch
                seen from height t) + drift. Its Toeplitz form is the Hilbert-type skew matrix, norm
                ≈ N/(πt) linear in N (geometric-growth prediction REFUTED), so −T^E ≻ 0 only for
                N < N₀(s) ≈ πt·log(t/2π)/(1−2σ) and not at every degree. Consequence: the non-ξ part of
                the constitution is positive only up to N₀; above it T^ξ's own far cluster must absorb
                the skew charge. The leaf is unchanged: RH ⟺ T^ξ ⪰ 0 at every degree (Gram). Register
                scale law: degree N resolves heights h ≈ N(1−2σ); the bottom is seen at N ≈ t/(1−2σ).
      THE SWEEP IDENTITY (626, Sam: "only the nontrivial zeros"; att626, 1e−28 per atom, 5e−7
                summed): Φ_s(z) = μ̂_0 + 2Σ μ̂_k z^k = Σ_ρ ω_ρ h(w_ρ z) = (2/d)[L(s_z) − i Im L(s)],
                s_z = (s + zc)/(1+z), L = ξ′/ξ; Re Φ_s(z) = 2Re L(s_z)/d. The disc is the channel, the
                circle the line, z = −1 height ∞. HENCE the full ladder at ONE anchor ⟺ seat mass ≥ 0
                on the whole channel ⟺ RH (Herglotz both ways, elementary). The degree-N constitution
                (622–625) IS the degree-1 mass constitution swept over the channel: 624's Poisson formula
                was the sweep; 625's Γ limit is the sweep reaching the bottom where Re E < 0. TAG: EQUIV;
                the register is an instrument (Cayley picture), not a new certificate family. Compile
                plan (identity only, ~200 lines): per-atom ring identity + `logDeriv_xiProductMult_partial_fraction`
                + `xi_logDeriv_sub_product_const_off_zeros` + r-damped `Real.circleAverage` formula.
      SWEEP COMPILED; VERDICT RETRACTED (627, `HerglotzSweep.lean`, standard axioms): `atomHerglotz_eq`,
                `xiHerglotz_eq` (Φ_s(z) = (1/d)[−L(s) − L(1−s̄) + 2L(s_z)]), `xiHerglotz_eq'`,
                `xiHerglotz_re` (Re Φ_s(z) = 2Re L(s_z)/(2σ−1)), `movedAnchor_re_lt_half_iff` (disc = channel).
                THE FREEDOM IT BUYS: the anchor. At Re s₀ < 0 every ingredient of the coefficient
                sequence is absolutely convergent and explicit (primes + Γ + clocks), and the sweep carries
                the one-anchor ladder into the strip by identity — rule 4 realised on the carrier. NEW LEAF
                SHAPE (STRONGER, constructive): exhibit the positive measure on the circle whose Fourier
                coefficients are the explicit sequence μ̂_k(s₀); discharge by identity. Owed: coefficient
                expansion + r-damped integral + Herglotz both ways ⟹ ladder at one anchor ⟺ RH.
                NEXT OBJECT: the explicit anchor's sequence from `logDeriv_xi_eq_arch_sub_lseries`.
      THE EXPLICIT ANCHOR COMPILED (628, `ExplicitAnchor.lean`, standard axioms): on Re s < 0,
                ξ′/ξ = −weilArch(1−s) + LSeries Λ(1−s) as functions (`xiLogDeriv_eq_explicit`); the jets
                of ξ′/ξ are the jets of this explicit function (`jets_xiLogDeriv_eq_explicit`); the prime
                jets are absolutely convergent L-series `(−1)^m/m!·Σ Λ(n)(log n)^m n^{s−1}`
                (`jets_primeSide`, Mathlib `LSeries_hasDerivAt` through the reflection); the Toeplitz
                coefficients split Γ + prime (`explicitAnchor_toeplitzCoeff_split`,
                `primeSide_toeplitzCoeff_succ`: Laguerre-type polynomial in log n per prime power); the
                sweep's Herglotz function is the explicit function at the moved anchor while Re s_z < 0
                (`xiHerglotz_explicit`), no zero in any hypothesis. LEAF (STRONGER, constructive): the
                explicit sequence μ̂_k(s₀) is a Carathéodory sequence — exhibit its positive measure.
                Owed: Γ jets as series (polygamma all orders), Herglotz both ways, then one-anchor ⟺ RH.
      Γ JETS AS SERIES, ALL ORDERS (629, `GammaJetsSeries.lean`, built, standard axioms):
                `hasSum_deriv_inv_pow_series` (termwise derivative of Σ(w+n)^{−k}, k ≥ 2, on a ball
                inside ℂ∖ℤ), `iteratedDeriv_digamma_series` (ψ^{(k)}(z) = (−1)^{k+1}k! Σ(z+n)^{−(k+1)},
                induction from Zeta23's trigamma), `hasSum_polygamma`,
                `iteratedDeriv_digamma_half_one_sub_series` (the anchor's variable (1−s)/2, Im s ≠ 0).
                `ArchSideJets.lean` (jets of 1/(s−a); `jets_archSide_series`: jets archSide s m =
                1/s^m + 1/(s−1)^m − Σ_{n≥0}(s−1−2n)^{−m}, m ≥ 2, Re s < 0, Im s ≠ 0; CAPSTONE
                `jets_xiLogDeriv_series`: every jet of ξ′/ξ at an explicit anchor = Γ-tick series +
                Laguerre-weighted prime series, no zero anywhere). With 628 the explicit anchor's whole
                coefficient sequence is series: Γ ticks 1+2n (−1), end 0 (+1), primes Λ(n)n^{s−1} with
                Laguerre weights. Owed: Herglotz both ways ⟹ one-anchor ⟺ RH.
      ONE ANCHOR'S LADDER ⟺ RH, COMPILED (630, `AnchorLadder.lean`, `LadderMinor.lean`,
                `LadderImpliesRH.lean`, standard axioms): `anchor_ladder_iff_rh (s ∉ zeros) (Re s < ½) :
                Ladder s ↔ RH`, Ladder = every Toeplitz form of hermExt(xiCoeff s) real and ≥ 0,
                xiCoeff s k = Σ_ρ m_ρ ω_ρ w_ρ^k. RH ⟹ ladder: Gram identity (`ladder_of_rh`). Ladder ⟹ RH:
                by growth, not Herglotz — minor bound ‖μ_k‖ ≤ μ_0 (`ladder_coeff_bound`), a channel zero
                has ‖w_ρ‖ > 1 (`one_lt_norm_transport_iff`), largest modulus attained on a finite set
                (`finite_transport_ge`), tail → 0 (dominated convergence), Cesàro of the finite
                almost-periodic sum ≠ 0 (`re_ge_half_of_ladder`), mirror symmetry. TAG: EQUIV, compiled.
                THE CERTIFICATE FAMILY: RH ⟺ positive-definiteness of one sequence at one point.
                Owed: atom sequence = jet sequence (S_m = Σ m_ρ(s−ρ)^{−m}, m ≥ 2, termwise differentiation
                of `logDeriv_xiProductMult_partial_fraction`), which makes 628's explicit prime-and-Γ
                sequence the one whose ladder is RH.
      REDUCTION CLOSED END TO END (631, `JetsAreAtoms.lean`, standard axioms):
                `iteratedDeriv_xiLogDeriv_series`, `toeplitzCoeff_jets_eq_xiCoeff`, and
                **`explicit_ladder_iff_rh (Re s < 0) : ExplicitLadder s ↔ RH`** — RH is the
                positive-definiteness of the explicit prime-and-Γ sequence
                `toeplitzCoeff d (jets (−weilArch(1−·) + LSeries Λ(1−·)) s)` at one point. No zero in any
                hypothesis. THE LEAF (the only node left, STRONGER-constructive): exhibit the positive
                measure on the circle with these Fourier coefficients. ATTEMPTED (att631): partial Euler
                sums p ≤ P have a negative computed N=6 eigenvalue at all 15 sampled cutoffs through
                P = 2·10⁶; N=4 changes sign across these samples. This does not settle every finite P.
                Each prime contributes (ℓ_p/|d|)I − T^{bary_p}, uniform minus positive. Next attempt needs the
                primes' Poisson barycenters recombined across p with the Γ face supplying the uniform
                (the explicit formula in the Toeplitz register). Not proved. Not a stop-claim.
      CARRIER IDENTITY + BOUNDEDNESS FORM (632, att632, `BoundedIffRH.lean`, standard axioms):
                on the carrier each prime is purely oscillatory — the uniform (ℓ_p/|d|)λ is exactly the
                m=0 Poisson term of ν_p (verified 1e−8 per prime); the transported measure is
                Γ density − (1/π)|s₀−½−iy|^{−2}·Re ΣΛ(n)n^{−½−iy}: Weil's criterion in the anchored class.
                COMPILED: `rh_iff_bounded`, **`explicit_bounded_iff_rh (Re s < 0)`: RH ⟺ the explicit
                prime-and-Γ sequence is BOUNDED in k** (growth rate = max_ρ ‖w_ρ‖). THE LEAF NOW: show
                sup_k |μ_k(s₀)| < ∞ for one anchor. Not proved; the fiber's cancellation events must lie
                on the carrier; the finite-cutoff experiments do not settle all finite constructions.
      POLYNOMIAL GROWTH CONSUMER (`SubexponentialAnchor.lean`, standard axioms; 2026-09-06 review):
                the maximal-atom argument needs only μ_k/R^k → 0 for every R > 1. COMPILED:
                `rh_of_subexponential`, `rh_of_polynomial_growth`, and the fixed-anchor consumer
                `riemannHypothesis_of_explicit_fixed_anchor_polynomial_growth` to Mathlib's literal RH.
                An alternative sufficient estimate is |μ_k(-1+20i)| ≤ C(1+k^p), with C and p fixed.
      NORMALIZATION AND CORRECTIONS (633, `SeatHerglotzSweep.lean`, standard axioms): exact
                `xiHerglotz_re_eq_scaled_seatMass`: Re Φ_s(z) = ((1−|z|²)/|1+z|²)·seatMass(s_z);
                `Gclock_re_pos` (Re G_β > 0 on the channel); `movedAnchor_inverse`. Owned corrections:
                626(ii) sign (Re G_r > 0), 631 finite-cutoff overclaim (evidence, not a law), 632
                distribution claim (coefficientwise; a tempered distribution ⟺ polynomially bounded
                coefficients ⟺ RH), 625/626 scale wording (far-height reach near the antipode).
                THE LEAF, FINAL FORM: RH ⟺ the fiber's resultant functional on the carrier is TEMPERED
                (one polynomial bound on one explicit sequence at one fixed point). Not established.
      THE EXACT GAP, COMPILED (634, `GrowthGap.lean`, standard axioms): unconditionally
                `explicit_growth_unconditional'`: ‖toeplitzCoeff(−3)(jets explicitLogDeriv(−1+20i)) k‖ ≤
                C·growthBase^k with growthBase = √(1+3/(1215/2−20)²) < 1 + 5·10⁻⁶ (`growthBase_lt`),
                from the compiled DVP height 607.5 (`online_below_1215o2`) and `norm_transport_sq`.
                RH = base 1 with a polynomial factor. Distance to RH at this anchor = the last
                4.35·10⁻⁶ of the growth base; verified height H gives base √(1+3/(H−20)²), never 1.
                Not proved. A proof needs an input beyond zero verification (Weil positivity in the
                anchored class); none supplied.
      STAGED TARGET AND THE END ATOM (635, `StageBoundStatus.lean`, standard axioms):
                `stage_bound_iff_polynomial_bound` — the staged Draft-B bound is EQUIVALENT to the
                completed Draft-A bound (limit transfer one way, constant C+1 the other), so staging is
                presentation, not weakening. `one_lt_norm_transport_anchor_zero`: the Archimedean END
                atom 0 (the reflected pole of ζ at 1) has ‖w‖ = √(1+3/401) = 1.0037 > 1;
                `norm_transport_anchor_tick_lt_one`: every Γ tick 1+2n is strictly inside. Hence the
                Archimedean side ALONE violates every polynomial envelope, and only a PAIRED estimate
                (prime divergence at the reflected point cancelling the end atom) can discharge the leaf.
                Rules out the split-estimate class of attempts. RH not proved.
                [635's framing was barrier-shaped and wrong (rules 9/11); superseded by 636, which
                performs the pairing instead of reporting the atom.]
      THE END PAIRING, CONSTRUCTED (636, `PairedSides.lean`, standard axioms):
                pairedArch = archSide − 1/s, atoms = Γ ticks 3,5,7,… only (`jets_pairedArch_series`);
                pairedPrime = 1/s + primeSide absorbs the ζ′/ζ pole at the reflected point;
                `pairedArchCoeff_atoms`, and **`pairedArchCoeff_bounded`: the Γ face's coefficient
                sequence is BOUNDED unconditionally** (every tick inside the closed disc, weights
                ≤ (n+1)^{−2}). Hence **`rh_iff_pairedPrime_polynomial`: RH ⟺ a polynomial bound on the
                paired PRIME coefficients alone** — the Archimedean side is out of the leaf. The leaf is
                now one arithmetic sequence: 1/s + Σ Λ(n)n^{s−1}, jetted and binomially transformed at
                −1+20i. Not proved.
                That estimate is not yet proved. Next construction: a finite-order bound for the
                completed carrier functional on w^k, identified with these explicit coefficients.
                Sweep normalization, review, and literal compiler output: `SWEEP_UPDATE_REVIEW.md`
                and `SWEEP_UPDATE_VERIFICATION.md`.
      THE ARITHMETIC BOUND ATTEMPTED (637, `tmp/att637_paired_prime_laguerre.py`, `tmp/att637b_planted.py`;
                pencil, no new Lean): the paired prime weights in closed form, exact —
                q_k(ℓ) = (−1)^{k+1}(ℓ/(k+1))·L_k^{(1)}(3ℓ) (rational check k ≤ 30) — so
                μ_{k+1} = ω₀w₀^{k+1} + ((−1)^{k+1}/(k+1)) Σ_n Λ(n) log n · n^{−2+20i} L_k^{(1)}(3 log n)
                = (−1)^{k+1} ∫₀^∞ e^{−(2−20i)u} P_k(u) d[ψ(e^u) − e^u]: the Laguerre transform at scale
                |d| = 3 of the prime remainder measure at critical normalization e^{−u/2}d[ψ(e^u) − e^u].
                Sequence computed four ways (Cauchy Taylor, atoms, primes to 10⁷, sweep generating
                function), agreeing to 6e−7; bounded ≤ 0.39 to degree 3000 while the end atom alone is 178.
                Pencil: |ψ(x) − x| ≤ C x^{½}(log x)^A ⟹ |μ_{k+1}| ≤ C′k^{A+3}; any exponent θ > ½ admits a
                remainder with exponential coefficient growth (planted e^{ρu} is the atom at 1 − ρ; base
                1.00033 at ρ = 0.6 + 50i). So in arithmetic the leaf IS von Koch's estimate — the node §2
                already carries ("Centering at the END lands on von Koch — EQUIV, unsigned"): RESTATEMENT,
                `rh_iff_pairedPrime_polynomial` EQUALS the von Koch node. Unconditional inputs: Zeta23
                `MediumPNT` (exponent 1 − o(1)) gives base e^{2/3} by the absolute route, strictly worse
                than the exact atom route's 1 + 4.35e−6 (634); the cancellation an arithmetic bound must
                produce is A_k/|μ_{k+1}| ≈ 16·e^{2k/3} (3.8e18 at k = 60). Not proved. Verdict: lateral.
      MIRROR PAIR UNDER TRANSPORT (646, `MirrorTransport.lean`, standard axioms): `transport_mirror`
                (w_{1−ρ̄} = (w̄_ρ)⁻¹), `atomWeight_mirror` (ω_{1−ρ̄} = ω̄_ρ), `pairCoeff_conj` (the pair's
                coefficient sequence is Hermitian), `pairCoeff_of_norm_one` (on the circle the pair
                collapses to 2Re(ω)·w^k). An off-line pair is the face-inversion pair (w, 1/w̄) with
                conjugate weights; its seat-form contribution is 2Re[ω C(w) conj C(1/w̄)]. The Hankel
                chart on a real strip anchor is indefinite under RH because the pole block's continuation
                across s₀ = 1 is minus a positive measure's moments (646). Identities only; no positivity.
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

**Guard verdict, 2026-09-07 (ledger 638).** The anchored transport that `hp_pencil.tex` names as
the candidate external bound on κ (the negative squares of the FE pairing) has been built and
measured (622–637): its growth base is sup_ρ ‖w_ρ‖ (634) and its bound is von Koch (637), so it
computes κ from the spectrum and is an instrument, not the exhibition. Every leaf under [HP]
remains EQUIV. The exhibition's required input now has a stated shape, in the paper's own frame:
a positivity proved on an object that is neither the zero set nor a finite truncation of the prime
series (the function-field model is the Hodge index theorem on C×C). No such object is compiled;
grep for "Hodge index" / "Castelnuovo" returns the paper's one sentence and C3's D7 door only.
The plan is still a proof plan modulo the one exhibition.

**Branch (B), opened 2026-09-07 on Sam's choice (ledger 639): the external bound on κ, written
backward from the target in the surface register of Weil's proof for curves.**

```
[B0]  κ = 0 for the FE pairing  ⟺  RH                       (289, spectralCoord_feReflect)   EQUIV
[B1]  THE SURFACE REGISTER — classes on carrier × anti-carrier and their pairings, DC first:
        H, V      the two ends (poles at 0 and 1)            pairings P₋ = ∫g e^{−u/2}, P₊ = ∫g e^{u/2}
        Δ         the diagonal                               Δ·Δ = "2 − 2g" = the archimedean DC (625),
                                                             the genus is infinite and grows as log t
        Γ_t       graph of the time-t flow (height shift)    Γ_t·Γ_s = e^{min(t,s)} N(|t−s|),
                                                             N = the fixed-point comb Σ Λ(n) n^{−½} δ_{log n}
                                                             + ends + archimedean = the explicit formula (534)
      Curve model: Γ_{F^m}·Γ_{F^n} = q^{min} N_{|m−n|}, N_k = 1 + q^k − Σ α_i^k, N_0 = 2 − 2g.       COMPILED
      (the pairings ARE the compiled explicit formula read as intersection numbers; no new theorem)
[B2]  CASTELNUOVO ON THE FLOW SPAN: for D = Σ a_t Γ_t, D² ≤ 2(D·H)(D·V).
      Pencil (this session, curve case exact): the pole terms of D² equal 2(D·H)(D·V) identically,
      so the inequality is Σ_i |b̂(θ_i)|² ≥ 0, i.e. RH for the curve. For ζ the same cancellation is
      Lemma A of the support certificate: Q(g) = 2Re(P₊P̄₋) + (1/2π)∫σ|Ĝ|².                    EQUIV
      Equality test: [B2] EQUALS Weil positivity (Track W, att239). Restatement in a new register.
[B3]  THE SUPPLY — a Hodge-index inequality on an AMBIENT object, proved without the spectrum,
      restricting to [B2] on the flow span.                           STRONGER-constructive (shape)
      Weil's proof needs three things the flow span does not contain: (i) an ambient divisor group
      with effective classes, (ii) Riemann–Roch on the surface (an existence theorem for sections
      with quadratic growth), (iii) effective classes pair non-negatively with ample ones. The
      Kähler proof needs instead: harmonic representatives + pointwise algebra on primitive (1,1)-forms.
      Candidates in the house, each run through the equality test (ledger 639):
        (a) unitary-clock Grams + the Poisson barycenter (520/624): PSD each, but the Euler mixture
            enters with wrong-sign DC per prime (631, 632); the compensation is the Γ face and the
            zeros' far field — spectral.                                                  census
        (b) monotone warps (pushforward of a positive clock measure is PSD): the warp is built
            from the zeros (the seat, 541); spectral.                                     census
        (c) harmonic representatives / Bochner: the kernel Σ_ρ e^{iγτ} is positive-definite iff
            the zero measure is positive; the harmonic representative IS the spectrum.    census
        (d) Riemann–Roch on carrier × anti-carrier with effective classes: no house object for
            RR or effectivity. Literature: Connes–Consani's Riemann–Roch strategy on the square
            of the scaling site (open; Connes survey 2602.04022 §4.1 read at source 08-17: no
            conceptual reason for positivity "when primes are involved").                  OPEN
        (e) WeilDuality.lean (2026-07-01, never ledgered): Weil I's engine COMPILED
            (tensor_power_purity, duality_forces_purity, purity_engine, purity_from_castelnuovo)
            with ONE input, "the helix Castelnuovo inequality" ‖T^k v‖² ≤ C·B^k·‖v‖² on the
            vanishing classes. Realized in the anchor register it is ‖w_ρ‖ ≤ 1 for every zero:
            EQUALS the growth leaf of 630/634, and 634 is its measure (holds with B = growthBase²
            in place of 1).                                                               census
        (f) ChiralCup.lean (2026-06-26): the cup form, a Gram form on ℕ →₀ ℂ, PSD by construction
            with a Hilbert completion — an AMBIENT positive form; its link to the vanishing classes
            (an operator on the cup space whose resolvent trace is the fiber's readout) is [HP].
        (g) NeronSeveriRung.lean (Hodge side): NS(E×E), rank 3, no Frobenius class — the
            cooperative-parameter surface in characteristic 0.                            model
      No candidate survives the equality test; (d) remains the un-walked construction. Absence
      claims here were checked by grep AFTER being written once (ledger 639 correction); every
      line above now cites the file it rests on.
```

First object of (B), if pursued: an RR-type count of sections on the house surface — the dimension
of the space of banks vanishing on a prescribed cell configuration — computed on the finite unitary
bank first (where the answer is known and RH holds by construction), then at support L for ζ.
The test it must pass before it counts as a supply: positivity of the pairing of an "effective"
class with every flow class, derived from the count alone, with no zero location used.

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
- **A1 DONE (2026-09-04)** — `RequestProject/XiIntegralIdentification.lean` proves
  `xiIntegral(z) = 2 * ξ(½ + iz)` for every complex `z`. The existing kernel and integral
  definitions require this factor of two. The proof integrates the derivative of
  `ψ′(u) cos(zu) + z ψ(u) sin(zu)`, with `ψ′(0) = -1/2`, and applies the compiled
  Mellin identity. `xiArithmeticStage U s := xiStage U (-I * (s - 1/2)) / 2` is entire;
  `xiArithmeticStage_value_and_derivative` proves convergence to both `ξ(s)` and `ξ′(s)`
  at every `s`, closing both analytic approximation clauses of the stage door.

**A3 DONE, A2 DONE (2026-09-01, ledger 519).** `SeatMassEtaForm.lean`: `logDeriv_Gammaℝ_eq`,
`logDeriv_riemannXi_splice`, `seatMass_eta_form`, `riemannHypothesis_of_eta_mass` — the mass
door restated on `η′/η − (1−2^{1−s})′/(1−2^{1−s}) + 1/s + 1/(s−1) − ½ log π + ½ Γ′/Γ(s/2)`.
`XiStageHolomorphy.lean`: `xiStage_hasDerivAt`, `xiStage_sub_xiIntegral_norm_le`,
`xiStage_tendstoLocallyUniformly`, `xiIntegral_differentiable` (entire),
`deriv_xiStage_tendsto`. **A1 is also compiled (2026-09-04)** with the normalization above.
The kernel checks for `xiIntegral_eq_two_mul_riemannXi`, `xiArithmeticStage_differentiable`,
and `xiArithmeticStage_value_and_derivative` report exactly
`[propext, Classical.choice, Quot.sound]`. The stage-mass sign and the carrier eigenvalue
correspondence remain separate construction targets.

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
½Γ′/Γ(·/2), and Σ Λ(n)(log n)^m n^{−s}. **No zero of ζ in the hypothesis.** Collected by n (596,
`PrimeSymbol.lean`, **`rh_iff_prime_symbol_nonneg`** [COMPILED both ways]): RH ⟺ ∀ γ, 1<σ₀<3/2, R(0)=0:
Re[ dcForm R s d − Σ'_n 2·Re(Λ(n) n^{−s} 𝒜_R(log n)) ] ≥ 0, s = σ₀+iγ, d = 2σ₀−1, with the symbol
𝒜_R(ℓ) = Σ conj(r_j) r_k primeSymbol d j k ℓ an explicit real polynomial functional (closed form
`pf_fst_closed`, all coefficients positive; 𝒜_R(0) = the 589 Pascal–Hankel form). **Identification
(pencil + numeric 8e−31; Lean integral owed):** 𝒜_R(ℓ) = ∫₀^∞ P_R(u+ℓ) conj P_R(u) e^{−du} du — the
autocorrelation of the one-sided Laguerre-type function P_R(u) e^{−(σ₀−½)u} e^{iγu} 1_{u>0}; the door
is Weil's functional on the anchored Laguerre class (unbounded support ⟹ full-strength iff). The DC is
the Gram matrix of that basis in L²(0,∞; e^{−du}) (positive definite); the AC is the phase clock with
autocorrelation weights and an ℓ-dependent phase. N = 1 carries no RH content (Re ξ′/ξ ≥ 0 for σ₀ > 1);
N = 2 is the first degree with a phase. Open node, in this register: the Gram-vs-clock inequality for
every P_R. Content of the door's hypothesis (590–591): the positivity is carried by the actual phases
γ·log p, enslaved to the zeros; free phases violate at every degree ≥ 2. Open node unchanged in content.

### 652 (2026-09-07) — compiled direction of ζ′ at an on-line zero
`GrowthDisplacementLaw.lean`: `deriv_zeta_online_reflect` ζ′(ρ) = −χ(ρ)·conj ζ′(ρ) (COMPILED, every on-line zero);
`growth_direction_eta` η(ρ−2)/η′(ρ) = B·(1−ρ)(2−ρ)/(4π²)·conj(ζ(ρ+2)/ζ′(ρ)) (COMPILED, simple on-line zero).
Serves the fiber's growth flow (650–651); no node on an off-line zero. Consumers: seat sign form, escort ladder.
### 653 (2026-09-07) — phase bound compiled
`PhaseBound.lean`: `phase_bound` 0 < Re(B·q·conj ζ(ρ+2)) and `growth_direction_re_neg` Re(η(ρ−2)/η′(ρ)·conj ζ′(ρ)) < 0
(COMPILED, simple on-line zero, |γ| ≥ 14; Euler product inside via `zeta_inSector`). The 651 law is fully machine-checked.
### 658 (2026-09-07) — sign-mechanism leaf: input identified
Seat on the channel = generating function of the Laguerre hierarchy J_n(t) (classical: Patrick 1973 / Csordas–Varga 1990;
verified 1e−15). Positivity is not site-local and not a kernel-shape property (measured, 658c/d): it is the cancellation of
the two-ended sites' cusps at the weld u = 0 (modular symmetry at the fixed point). LEAF INPUT REQUIRED: the weld
smoothness entering the Laguerre hierarchy — order of cusp cancellation vs power of 1/t. Status: EQUIV, input named.
### 659 (2026-09-08) — new sub-node under the sign-mechanism leaf: RUNG 1 = "RH near the line"
Rung 1 of the Laguerre hierarchy (L(Ξ) ≥ 0 ∀t) ⟺ Re[(ξ′/ξ)′(½+it)] ≥ 0 ∀t (second jet of the seat's complex form on the
carrier ≥ 0). Consequence (derived, Hadamard): any off-line zero satisfies (β−½)² ≥ 2/Σ_{others}Re 1/(γ−τ)², i.e. repelled
from the line by the local density, ≈ |β−½| ≥ 4.9/log(γ/2π). Measured: bank-level L(Z) > 0 on [10,1000] (far end never
load-bearing; density ≫ curvature). Tag: NECESSARY (weaker than RH); inputs: on-carrier jets + far-end curvature;
proof status: not in record; literature: Csordas–Varga 1990, Csordas–Smith–Varga 1994 (not re-read).
### 661 (2026-09-08) — mirror transport of the derivative, GRH fibers (COMPILED)
`MirrorDerivativeTransport.lean`: Λ(s₀, χ⁻¹) = 0 ⟹ Λ(1−s₀, χ) = 0 ∧ Λ′(1−s₀, χ) = −N^{s₀−½} ε(χ) Λ′(s₀, χ⁻¹), every zero,
functional equation only. Next: Schwarz reflection for `completedLFunction` → on-line direction identity for characters.
### 662 (2026-09-08) — growth-resolution of multiplicity (node: one event per height)
m-fold limit event ⟺ m finite-head events at ρ + Z^{−2/m}(η(ρ−2)/c_m)^{1/m}ω^k (from F_Z = η − Z^{−2}η(s−2) + …).
Simplicity ⟺ convergence rate Z^{−2} at every zero. Sam's "no exact equality twice at a height" is exact at finite head.
### 664 (2026-09-08) — RH from ONE VANISHING PER HEIGHT (COMPILED reduction)
`OneVanishingPerHeight.lean`: for a real cascade converging to ξ, one vanishing per height ⟺ SourceLabelled, and
`rh_of_oneVanishingPerHeight`. Inputs still to write: the fiber cascade instance (convergence to ξ) and the principle on its stages.

## BURNDOWN (2026-09-08) — final task list to RH via `rh_of_oneVanishingPerHeight`
Compiled reduction (664): for a `MidpointCascade C` (stages entire, converging locally uniformly to ξ(½+iz)),
`RealStages C → OneVanishingPerHeight C → RiemannHypothesis`. Everything below serves its two hypotheses.

### Critical path
- **T1 — the fiber cascade instance `C_fiber : MidpointCascade`.** Stages = transforms of the two-ended site sums
  Σ_{m≤N} g̃_m (or a smooth-weld variant, see T2). Sub-tasks:
  - T1a  ξ's kernel representation in Lean: ξ(½+iz) = ∫Φ(u)e^{izu}du with Φ built from Jacobi theta (Mathlib has the
         theta functional equation and `completedRiemannZeta` via a Mellin pair; the kernel form needs two integrations
         by parts and the evenness of Φ). STATUS: not in Mathlib, not in tree. Size: large.
  - T1b  each stage entire (parameter integral of a super-exponentially decaying kernel). STATUS: to write. Medium.
  - T1c  locally uniform convergence of the stages to ξ (dominated convergence, Σ_m sup|g̃_m|e^{|Im z||u|} summable).
         STATUS: to write. Medium.
  - T1d  `RealStages C_fiber` (kernels real and even). STATUS: to write; easy once T1b exists.
- **T2 — `OneVanishingPerHeight C_fiber`: every stage has at most one vanishing per height.** THE CONTENT.
  - T2a  Decide the cascade. Measured (660): the cusped two-ended sums C_N lose zeros beyond a crossover height
         (C_1 keeps 1 of 13 real zeros below 60; C_2 keeps 7); the missing zeros are elsewhere in the plane. If they
         are non-real, each comes with its conjugate at the same height and T2 FAILS for that stage. TASK: locate the
         missing zeros of C_1, C_2 in a wide box with mp-precision nodes. Pre-registered prediction: non-real
         conjugate pairs at |Im z| ≳ 1 ⟹ the cusped cascade cannot serve T2; the cascade must have a smooth weld.
  - T2b  Choose stages with a smooth weld that CONVERGE to Φ (Pólya's product family is real-rooted in range but is a
         model: P_1(0) = 0.0385 vs Φ(0) = 0.4467, 660). Candidates: (i) two-ended site sums with the weld smoothed by
         the modular partner terms (the theta transformation applied to the tail, so each stage is smooth at u = 0
         and the sum is still Φ); (ii) the positive amplitude warp e^{λu²}Φ, λ ↓ 0 (real-rooted for λ ≥ 0.22, Polymath;
         convergence to Φ is the λ → 0 limit; real-rootedness for all λ > 0 is RH by Rodgers–Tao's Λ ≥ 0).
         STATUS: (i) unbuilt; (ii) known, and its T2 is the theorem.
  - T2c  Prove T2 on the chosen stages, all heads, all heights. STATUS: open; this is the clause. Instruments: rung 1 as
         the merger detector (659), the growth-resolution lemma (662), the mirror transport (661), inertness of
         admission (662c), the seat as the Laguerre generating function (658).

### Supporting formal debt (lateral, finite)
- S1  Schwarz reflection for `completedLFunction` (absent from Mathlib) → GRH version of 652's direction identity.
- S2  Compile the growth-resolution lemma (662) from the Mellin expansion of the smooth-entry fiber.
- S3  Compile the seat = Laguerre generating identity (658; Patrick 1973) and rung 1 ⟺ Re(ξ′/ξ)′ ≥ 0 on the line.
- S4  Compile |ε(χ)| = 1 (root number modulus; stated in Mathlib's docstring, no lemma).
- S5  Wire the bounded discharge (`online_below_1269o2`) into the 663 transfer file for |Im ρ| ≤ 634.5.

### Order
T2a (decides the cascade) → T2b (build it) → T1a–T1d (compile the instance) → T2c. S-items in parallel.
#### BURNDOWN update 2026-09-08 (ledger 666)
- T2a DONE: cusped sums shed conjugate pairs beyond their crossover (C_1: 8 pairs located to Im 25; C_2: 2 past 37);
  the cusped cascade is not source-labelled.
- T2b DECIDED: the flow cascade C_flow, stages Ξ_λ = ∫e^{λu²}Φ e^{izu}du, λ_n ↓ 0 (partial-sum smoothings fail:
  Gevrey tails, √N divergence, or inheritance of Ξ's zeros).
- Remaining critical path: T1 (flow cascade instance; T1a kernel representation of ξ), then T2c = one vanishing per
  height for Ξ_λ at every λ ∈ (0, 0.22) — known for λ ≥ 0.22 — i.e. no first collision at positive warp.
#### BURNDOWN update 2026-09-08 (ledger 667): T1a steps 1–2 compiled (`XiKernelMellin.lean`): Λ(s) = 2∫e^{su}Ψ(u)du for Re s > 1.
Remaining T1a: step 3 IBP ×2 (Ψ″+Ψ′, boundary limits), step 4 evenness of K from the theta FE, step 5 continuation to all z.
#### BURNDOWN update 2026-09-08 (ledger 668): T1a scaffolding compiled (`XiKernelTheta.lean`): Ψ_reflect, holomorphic extension PsiC on |Im w| < π/4, all derivatives on the axis. Next: integrability + boundary limits, then the two IBPs.
#### BURNDOWN update 2026-09-08 (ledger 669): T1a step 4 compiled (`XiKernelEven.lean`: Kker_even). Remaining: step 3 (IBP), step 5 (continuation), then T1b–d.
#### BURNDOWN update 2026-09-08 (ledgers 671–672): T1a step 3 compiled (`XiKernelIBP.lean`: xi_integral_form). Remaining: step 5 (entire K-transform + identity theorem), then T1b–d.
#### BURNDOWN update 2026-09-08 (ledger 673): **T1a COMPLETE** — `xiSection_eq_Ktrans`. Remaining: T1b–d (flow cascade instance), then T2c.
#### BURNDOWN update 2026-09-08 (ledger 674): **T1 COMPLETE** — `rh_of_oneVanishingPerHeight_flow`. Remaining: T2c only
(one vanishing per height on Ξ_{1/(n+1)} for every n; stages n ≤ 3 covered by Polymath's λ ≥ 0.22 on paper, not in Lean).
#### BURNDOWN update 2026-09-08 (ledger 676): REGISTER DOOR compiled for all heights — `rh_of_registerIdentity : RegisterIdentity → RH`
(`RegisterIdentity` = at every good height ≥ 10 a ladder with exactly the census count of sign changes). T2c now has two
compiled forms: `OneVanishingPerHeight flowCascade` (cascade chart) and `RegisterIdentity` (register chart).
#### BURNDOWN update 2026-09-08 (ledger 677): **LIMIT DOOR** — `rh_of_smultIntegralSublinear : (∀ ε>0, ∀ᶠ T, −εT ≤ ∫₀ᵀ S_mult) → RH`,
Littlewood consumed unconditionally (`littlewoodBound_holds`). T2c in its weakest compiled form: the on-line ledger's
running integral is not linearly negative.
#### BURNDOWN update 2026-09-08 (ledgers 679–681): warped chart of T2c — head law (fiber decides the band iff Z ≥ T),
bank identity F_Z = F̃_Z − 2^{1−s}F̃_{Z/2} (END terms cancel), atom-flow road ATTEMPTED and refuted by computation
(atoms cross the carrier at Z ≈ t/2). Open clause unchanged: |F_T(s)| > 0 on the band below the head = η's band
zero-freeness.
#### BURNDOWN update 2026-09-08 (ledger 685): T2c constructive leaf = FLOW FRONTIER. `rh_of_flowFrontier` compiled;
RH ⟺ FlowFrontier λ₀ ∀ λ₀ > 0. de Bruijn = FlowFrontier (1/8) [to compile: strip narrowing]; Polymath = FlowFrontier 0.055.
Open part after de Bruijn: λ ∈ (0, 1/8) — a bounded parameter interval.
#### BURNDOWN update 2026-09-08 (ledger 687): Littlewood's radial identity COMPILED (`integral_SAll_eq_radialLogMass_sub`);
residue identity; fifth door `rh_of_radialNoResidue` (crossing-driven cumulative warp = radial log-mass difference ⟹ RH).

#### BURNDOWN refinement 2026-09-09 (ledger 677/687 coordinate layer)
`RequestProject/LogHeightRegistration.lean` transports the integrated registers through
the carrier's event-height coordinate `t = log Z`, with measure `dZ/Z`.
`integral_logHeight_register_split` retains the exact off-line multiplicity integral;
`smult_logHeight_lower` transports Littlewood's lower bound with that correction retained.
The six declarations passed `lake env lean RequestProject/LogHeightRegistration.lean`
(exit 0), with only `[propext, Classical.choice, Quot.sound]`; literal output is in
`proof-drafts/LogHeightRegistration20260909.txt`. This fills the coordinate-transport
layer of the limit route. It does not discharge the averaged lower bound in ledger 677.

#### BURNDOWN update 2026-09-10 (ledgers 696–698): the averaged door's ladder
- 696a: `PrimeCrossingMeanAgreement c` (prime-forced strain vs crossing ledger, in the mean; no chart object) ⟹ RH;
  697: it is an iff (`primeCrossingMeanAgreement_iff_rh`). Tag EQUIV.
- 698: the door lives on the COUNT axis, `∫₀ᵀ N_off = o(T)` ⟺ `N_off ≡ 0` — **no rung between door and theorem**.
  The DEPTH axis (678's fourth door, `Σ(β−½)⁺ = (1/2π)∫log|Z| + O(log T)`) has rungs: 0 ⊃ O(log T) ⊃ o(T) ⊃ O(T)
  [Selberg 1946] ⊃ O(T log log T). Its open rung o(T) ⟺ `N(½ + A/log T, T) = o(N(T))` for every fixed A (almost
  all zeros within o(1) spacing) — the middle band / sub-pair resolution of the primes, closed at current technology
  in ledgers 137–162, 502. Forward at THIS door requires an identity for the fiber's crossing count from the primes
  with no zero sum; none in the record. Verdict lateral; the deliverable is this state.
- 699 (Sam: "hp style proof … you are approaching the proof of rh via some weird vector"): 677–698 were a CHART vector.
  The node is E3 in the frame's words (every zero of ξ is a fiber vanishing at a real height Z, y = log Z); its exact
  compiled residual is the drift i(Re ρ − ½) on the native mode (`NativeCarrierTransport.full_operator_transport`,
  09-09). Constructive leaf unchanged: T2c `FlowFrontier`. Its next compile (de Bruijn strip narrowing) is STARTED:
  `DeBruijnStripStep.lean` has the polynomial shift step (no ledger entry until 699). Remaining: entire-function
  limit, heat operator as shift limit, assembly ⟹ `FlowFrontier (1/8)`, stages n ≤ 7 discharged at all heights.
- **700 (2026-09-10): COMPILED — `flowFrontier_one_eighth : FlowFrontier (1/8)`** (`DeBruijnFlowFrontier.lean`, with
  `HurwitzLimit`, `StripShiftClass`, `FlowCoshStages`, `XiStripApproximants`; standard axioms, build green). Stages
  n ≤ 7 of the cascade (`flowCascade_realRooted_of_le_seven`) are real-rooted at EVERY height — the first all-heights
  discharge of any stage. Zero-side input: the Hadamard product with paired exponential cancellation only.
  **T2c open part is now λ ∈ (0, 1/8).** Next classical input: Ki–Kim–Lee / Polymath 15 (`FlowFrontier 0.055`), not
  compiled; below 0.055 nothing classical is known. Tag of stages n ≤ 7: COMPILED; stages n ≥ 8: OPEN.
- **701 (Sam: "the helix geometry doesn't even have a strip"): 700 is CHART-FRAME — an instrument of the flow chart,
  not a geometric node.** The flow cascade itself is a chart object (transforms of a flowed kernel). The geometric
  program's clause is E3 in the transport register: `full_operator_transport` gives `K∘A = H∘K − i·K∘D`; RH ⟺ `D = 0`
  on the transported modes. Open decision (Sam): keep T2c in the flow chart, or rebuild it on a warp the geometry owns
  (growth head `W(y)` / the S-warp), clause "one clean cancellation per carrier height".
- **702 (Sam: rebuild on the growth head): T2c REBUILT — `GrownFiberDoor.lean`: `HeadClean carrierHeads ↔ RH`**
  (`rh_of_carrierHeadClean`, `carrierHeadClean_iff_rh`; standard axioms). Cascade = the carrier's grown fiber
  `finiteFiber (physicalHead n)`; clause = no event in any compact far-side region once the head has climbed past it
  ("one clean cancellation per carrier height", the two ends). Convergence of the grown fiber to the readout compiled
  (`GrownFiberConverges.lean`: the fiber is the window-weighted average of the ordered bank's partial readouts). Tag
  EQUIV. Leaf (STRONGER, finite per region): an explicit head `Z₀(K)` past which no event sits in `K`. The flow-chart
  T2c (674–700) stays as an instrument; the frame's T2c is this one.
- **703: T2c's OBJECT IS FINAL — the TWO-ENDED grown fiber `twoEnded Z s = F_Z(s) + χ_η(s) F_Z(1−s)`.** Measured
  (att703): at heads 25–1000 every event in `[0.2,0.8]×[10,50]` is on the axis (10 = 10 = ζ's ten), none on the far
  side; the second end pins the events to the axis (the one-ended fiber's sit `Z^{−2}` off it). Compiled
  (`TwoEndedFiber.lean`): η's own FE `χ_η(s)η(1−s) = η(s)`, convergence to `2η` on the strip, the clause
  `TwoEndedClean` (one clean cancellation per carrier height, at every head, in every box) and the door
  `rh_of_twoEndedClean`. Per-stage clause = a finite decidable statement (box count = sign-change count). Owed: stage
  symmetry + reality on the axis (exact identities); converse needs simple zeros + a counting lemma. Tag EQUIV-or-
  stronger. The standing target is unchanged: the constitutional reason the balanced fiber's events cannot leave the
  axis.
- **704: FE symmetry and axis reality COMPILED** (`TwoEndedSymmetry.lean`): `twoEnded_one_sub` (the stages satisfy η's
  functional equation exactly at finite head), `chiEta_norm_one` (|χ_η| = 1 on the axis, from FE + conjugation),
  `twoEnded_sq_axis` / `twoEnded_axis_real` (the stage is a unimodular rotation of a real function on the axis). The
  per-stage clause is now "the box zeros of G_Z are the sign changes of the real u_Z" — finite, decidable per (T, Z).
  Still owed: the converse of the door (simple zeros + a counting lemma); the relation ω = e^{i(ϑ+φ)} to the
  Riemann–Siegel theta (duplication formula; not needed).
- **706 (Sam: "bring in the winding"): the winding enters the two-ended fiber through the MULTIPLICATIVE face —
  `WindingTwoEndRatio.lean` (standard axioms).** `E_x = exp L_x` (Riesz-tapered log-Euler product at front x),
  `G_x = E_x + χ_η E_x(1−s)`, ratio `R_x`; a balanced event is `R_x = −1`; `log‖R_x‖ = log‖χ_η‖ + Re L_x(1−s) − Re L_x`
  EXACT; slope across the axis = `2Σ w_xΛ(n)n^{−½}cos(t log n)`, so first-order far-side domination ⟺
  `D_{R,x} − END_x ≥ 0` (568 without the pole); domination ⟹ all events on the axis (compiled). MEASURED: Riesz
  fronts 10²–10⁴ keep 10 = 10 events on the axis, but domination fails on 2–6% of heights — exactly in the pole's
  shadow (period 2π/log x, amplitude x^{½}/(πt² log x)); `D_{R,x}` with the pole is ≥ 0 at every front (567
  reproduced). Sharp cutoff: off-axis events proliferate (32, 294). Verdict LATERAL: the pure ends+winding sign
  mechanism (517) is refuted in the pole's shadow; forward needs a multiplicative face carrying the pole (η's
  conduction comb) so that its two-end domination is `D_{R,x} ≥ 0` itself, then a reason for it that is not the
  zero comb. Not a stop-claim; the identity check for the pole-carrying face is pre-registrable and not run.
- **707 (Sam: "you aren't warping, are you"): NO — 702–706 were unwarped (growth law W only). Warp applied:**
  warped log-face `L_x + Π_x`, `Π_x′ = K_R(1−s)` (pole's Riesz kernel; `Π_x = −Ei(L(1−s)) + (x^{1−s}−1)/(L(1−s))`);
  two-end slope `κ^w = −2π D_{R,x}` EXACTLY (568 with the pole; 1.8e−15). Measured: κ^w < 0 at every height at
  fronts 10²–10⁴ (max −0.0073), events 10/0/10; finite-δ domination second-order-fragile at 10⁴ (δ = 0.05: 99.75%).
  END-TERM DC LAW fifth instance. Compiled object corrected: `chiZeta = feFactor⁻¹` (ζ's factor) — the first build
  paired the pure face with `chiEta` (formal theorems held; object mismatched the measurement).
- **708 (Sam: "carrier scaling and fiber warp apply at the same time"): front slaved to height by the head law
  (`physicalHead ≥ 9e^{2y}`, 556): `x(t) = 9t²`.** The two-ended warped multiplicative fiber at its own head is ONE
  real function of t; clause `D_{R,9t²}(t) ≥ 0`. Measured [10,100]: min D = +0.00164; 29 = 29 events, station − zero
  RMS 0.0062 (0.002 spacings), max 0.012, no zero data. Pencil: one-variable clause ⟺ RH (off-line dip
  `(9t²)^δ/(Lδ²)` beats the comb). Rung below: unconditional Weil positivity reaches support log 2 (Yoshida; house
  log 3) = fronts ≤ 3, never the carrier's head ≥ 900. Verdict LATERAL; forward needs a reason for the inequality
  that is not the zero comb. Next pre-registrable test: the margin law of `min D_{R,9t²}` over [T, 2T].
- **709 (Sam: "positivity means non-negativity; run the margin test only if certain of its value"): clause is
  `D ≥ 0`; margin test NOT run (Fejér valleys dip to 0 harmlessly — no decision value). CORRECTIONS to 708:** (i) the
  compiled head at ordinate t is `physicalHead t ≥ 9e^{2t}` (y = ordinate; `kClimb = e^y/p`); 708's `9t²` was a
  stand-in. (ii) 708's "EQUIV by pencil" RETRACTED by its own zero-side control (att709/709b): an FE-consistent merged
  pair `½ ± δ + iγ₀` is detected by the slaved-front register only for `δ ≥ δ*(γ₀)` — stand-in: `A₀ = δ*·log 9γ₀²` =
  0.33/0.49/0.46 at γ₀ = 10²/10³/10⁴; compiled head: δ* = 1e−4/2e−6/6e−8. So `D_{R,x(t)}(t) ≥ 0 ∀t` at ANY slaved
  front is a DEPTH-AXIS RUNG ("all zeros within δ*(γ) of the axis"), not RH; RH = the fully grown (∀x) fiber, 568.
  Free front confirmed: δ = 0.02 at γ₀ ≈ 1000 detected from L = 50 on. Verdict lateral; the rung is named, nothing
  classical walks it; forward = a reason for `D ≥ 0` at every front that is not the zero comb.
- **710 (Sam: "run that test"): MARGIN LAW measured.** Stand-in front 9t²: m(T)/(ϑ′/π) ≈ 0.015, FLAT T = 80…2560
  (my "shrinking" prediction refuted; minimum at a Fejér null of the nearest zero, gap 1.3–1.6× mean: the nulls sit
  at gap midpoints because 2π/L ≈ ḡ/2). Compiled head 9e^{2t}: m ≈ 1.5e−3·ℓ²/T (as predicted). D ≥ 0 everywhere;
  prime side = zero side to 1e−4. Comb statistics under RH; lateral.
- **711 (2026-09-11, Sam: "project 3D → 2D → 1D and land on anything besides a line?" NO — compiled):**
  `ProjectionLandsOnLine.lean`: `range_chartReadout : Set.range chartReadout = {ρ | ρ.re = ½}` (image of the full
  chain is exactly the line; radius and angle booked; abscissa = area-law output, not a coordinate);
  `not_chartReadout_of_re_ne`, `offLine_zero_not_chartReadout`. Standard axioms. §0a forward direction, one statement.
