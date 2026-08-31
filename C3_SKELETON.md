# C3 BACKWARD SKELETON (rule 11 — the primary artifact)

Written from the last line backwards; every node tagged `COMPILED` / `EQUIV` / `STRONGER` /
`OPEN` / `REFUTED` with its citation. Promoted from `tmp/claude_c3_long_batch_20260824.md:387`
on 2026-08-27 with the batch-27 O-lane folded in and the four audit corrections of that date
applied. Every live-repo citation re-grepped 2026-08-27.

**Update law:** every session either fills a node or refines this skeleton. Work with no slot
here is named as such *before* it is done. Any node claimed open carries a ledger number and
either a compiled theorem name or an explicit "grep returned none."

```
[TARGET]  ∀ ρ ∈ ZD.NontrivialZeros, ρ.re = 1/2                                    (RH)
   ↑ COMPILED  rh_of_xiStructure_isHB        RequestProject/XiStructureFunction.lean:109
[N1]  IsHB xiStructure                                                     EQUIV (= RH)
   ↑ COMPILED  rh_iff_xiStructure_dominates  RequestProject/XiStructureSeatBridge.lean:316
        (non-strict domination iff; the STRICT sign iff is
         isHB_xiStructure_iff_halfplane, …SeatBridge.lean:94 — distinct strengths)
[N1'] ∀ Im z > 0,  ‖E* z‖ ≤ ‖E z‖   (non-strict)                           EQUIV (= RH)
   |
   ├── ROAD A — the seat (region-valued, forward from proven regions)
   |   [N2]  0 ≤ Re[ξ(s)·conj ξ′(s)] on Re s > 1/2  (FE-mirror of the
   |         seat convention Re[ξ′/ξ] ≤ 0 on Re s < 1/2)                   EQUIV (= RH)
   |      ↑ COMPILED  seat_energy_re_eq      RequestProject/DVPSeatRealPart.lean:76
   |      ↑ COMPILED  re_logDeriv_mul_normSq …SeatBridge.lean:~100 (numerator↔quotient, re)
   |   [N3]  seat energy ≥ 0 at every admissible anchor                    EQUIV (= RH)
   |      ↑ COMPILED  seat_criterion_iff     RequestProject/SeatScalarCriterion.lean:702   [RH_LEDGER 293]
   |      ├─[N3a] |Im w| > 1/2               COMPILED unconditional
   |      |        seat_energy_nonneg_of_outside_strip  SeatScalarCriterion.lean:1004  [RH_LEDGER 296]
   |      ├─[N3b] |Re w| ≥ e⁴+2, depth ≥ ½−c/log   COMPILED unconditional
   |      |        seat_interior_rung_one'   DVPSeatRungOne.lean:953        [RH_LEDGER 340]
   |      |        ⇒ xiStructure_dominates_interior_rung  …SeatBridge.lean:288
   |      └─[N3c] shallow channel + bounded box (heights < 57 = census
   |               territory, classical to 3·10¹², NOT compiled)            OPEN — the residual region
   |
   └── ROAD B — the theta identity (identity-valued, backward from the sign)
       [N1″] RH ⟸ numerator sign on the strip 0 < Im z ≤ 1/2
          ↑ COMPILED 2026-08-27  rh_of_chart_numerator_im_nonpos
             RequestProject/XiNumeratorSeatWiring.lean:145 — footprint
             [propext, Classical.choice, Quot.sound], build green (8828 jobs).
             The strip reduction: seat_criterion_iff + N3a outside the strip
             + seat_energy_re_eq + rotation identity + conj-anchor symmetry
             + the numerator→quotient bridge (im-flavor of re_logDeriv_mul_normSq;
             Lean x/0 = 0 makes it hypothesis-free). Discharges the audit-F1
             strip→halfplane gap and the audit-F2 missing edge in one file.
             ★ SEAM CLOSED 2026-08-28 ★  rh_of_outer_band (scratch
             lib/B27O108.lean, std axioms): xiChart_reconciliation is rfl
             (both charts are ZD.riemannXi (1/2 − I·z)) and the band rung
             composes with the wiring in ONE build:
               RH ⟸ (numerator sign on 3 < |Re z|, 0 < Im z ≤ 1/2).
             The inner band is discharged; the compiled residual of Road B is
             the OUTER BAND alone.  (Physical file port into RequestProject
             remains optional hygiene; the composition is compiled.)
       [N4]  Im[Ξ′(z)·conj Ξ(z)] ≤ 0  on  0 < Im z < 5/2                   EQUIV (= RH, given N1″)
          |   Exact reformulation: Khat = ½·∂_y|Ξ(x+iy)|² — the sign IS modulus
          |   monotonicity off the critical line (identity; lemma-candidate, not yet compiled).
          ↑ COMPILED  numerator_folded       scratch lib/B27O59.lean:207    [LEDGER_O_E59]
             — exact theta identity, three independent Fubini routes (A/B/C), 62/62
               printed footprints std (63rd theorem covered transitively), verified
               numerically 14/14 decidable + 40 digits at dps 50 (x=20), 19 digits (x=50)
       [N5]  0 ≤ ∫_{s>0} ∫₀ˢ twoTerm x y s d  ds   for  0 < y ≤ 1/2        EQUIV (= RH)
          ├─[N5a] slice_nonneg_of_moment / _of_parts   COMPILED conditional dischargers
          ├─[N5b] cell 0: |x|·s ≤ π/2  COMPILED unconditional  B27O59.lean:548
          |        THE SHARP π-CELL: COMPILED 2026-08-27 — the full chain:
          |        numerator_pos (O53 gate) + termwise slope signs → turan_all
          |        (O67/O68, whole half-line) → logDeriv antitone → dKernel_antitone_in_d
          |        (O69, closed [0,s]) → cosPart_nonneg_of_pi (O70, reflection pairing).
          |        Sharp: the s→0 limit forces π (prework X2, ratio → 1.000380).
          |        Geometric reading: the pitch contraction never slackens.
          ├─[N5c] pointwise-in-s slice positivity     REFUTED by measurement:
          |        slice(x=400, y=1, s=0.9) = −6.155e-5 < 0 (o59_fast2 TEST B) and
          |        compiled model_slice_neg (kernel-free model provably negative)
          |        ⇒ the argument must be s-AVERAGED and must use the theta kernel
          ├─[N5d] integrability of the s-marginal     COMPILED 2026-08-27
          |        folded_marginal_integrableOn  scratch lib/B27O65.lean — Fubini
          |        marginal of the O57 wedge-indicator integrability
          └─[N5e] the X₀ rung: Khat ≥ 0 for |x| ≤ X₀
                   ├─ X₀ = 1/2  COMPILED 2026-08-27  numerator_im_nonpos_band
                   |   scratch lib/B27O66.lean — Im[Ξ′·conj Ξ] ≤ 0 on |Re z| ≤ 1/2,
                   |   0 < Im z ≤ 1/2; std axioms; 38 theorems across B27O61–O66
                   |   (head window ≥ 6y·e⁻³⁰ vs tail ≤ 642y·e⁻⁴¹, five orders spare).
                   |   First unconditional region on Road B, species of N3b.
                   ├─ X₀ = 3    ★ COMPILED 2026-08-28 ★  numerator_im_nonpos_band_three
                   |    (scratch lib/B27O107.lean, std axioms, escape-scans clean):
                   |    Im[Ξ′·conj Ξ] ≤ 0 on |Re z| ≤ 3, 0 < Im z ≤ 1/2 — the
                   |    6× extension of rung 1, fully unconditional.  Chain:
                   |    O103 pointwise layer (5 slice bounds) → O104 glue
                   |    (sinh envelopes, piece_integral_ge, Ioi-split) → O105
                   |    evenness → O106 strip numerics (35 thms: 6 head mass
                   |    floors k=0..5, 12 tail ceilings at dumped anchors, 10
                   |    two-sided cosh envelopes) → O107 assembly (27-piece
                   |    fold of (0, π] + O65 Ioi-π handoff; certified budget
                   |    head 4.45e-4·y vs deficits 2.85e-4·y, NET +1.6e-4,
                   |    asserted in exact rationals at emission).  Session
                   |    total O77–O107: ~700 theorems, all std axioms.
                   |    Historical plan note (superseded by the compile):
                   |    PLAN CLOSES, 2.84× engine-exact margin (o79 v4,
                   |    2026-08-27; supersedes the o73 bookkeeping).  c-BAND design:
                   |    tile in rational c = w/s bands ((1+c₁)xs ≤ π ⟹ w ≥ c₁s),
                   |    which dissolves the x-extent entirely (the (x,s)-tile grid
                   |    was exponentially lossy, logslope −13); ONE band tile per
                   |    s-strip, 17 strips on [0.524, 1.571].  CORRECTED: the
                   |    "far tail s > π/3 tiny" note was a FALSE rung-1 import —
                   |    certified tail 1.79e-4·y ≈ head order; closes via
                   |    first-moment tail staircase + two-window N=6 head
                   |    (5.76e-4·y vs 2.03e-4·y total deficits).  Engine COMPILED:
                   |    t0_lo (O76) + t0_hi_sharp (O78), validated end-to-end at
                   |    t₀(1/2) ∈ [0.0294, 0.031] (O77, std axioms).  COMPILED
                   |    2026-08-27 (all std axioms, escape-scans clean):
                   |    slice_nonneg_of_band + floor_ge_on_band + mass piece
                   |    mirrors (O80); 6-piece staircase (O81); anchors e^k to
                   |    k=66 (O82); ALL 451 t₀ point enclosures (O83–O101,
                   |    generated, engine-exact constants, zero failed points
                   |    after one tactic swap); ALL 17 strip staircases + 17
                   |    band tiles (O102) — the tiled interior of the window is
                   |    done: each tile_i + slice_nonneg_of_band gives slice ≥ 0
                   |    on strip × {(1+c*)xs ≤ π}.  Remaining: two-window head
                   |    assembly, tail-strip assembly, wedge budget, final
                   |    integral assembly → numerator_im_nonpos_band_three
                   |    (mirror of rung_one's Ioc/Ioi split).  Cell register
                   |    throughout; the O70 pairing IS the antipodal map.
                   |    COMPILED toolkit: O69 antitone, O70 π-cell, O71 Φ-suite,
                   |    O72 |cos|-cancelled criterion, O73 staircase, O74 near
                   |    enclosure, O75 scaled nodes + tile floor, O76/O78 engine.
                   |    Head-vs-deficit REFUTED as the assembly shape (prework v1).
                   └─ X₀ ≈ 8    OPEN — Route B split domination (T1>|T2| measured
                        through x ≈ 8, o60 PROBE I)                              [task 3]
       [N4c]  S_x(r) ≥ 0 pointwise (old Wigner route)                       REFUTED ✗ false

   ├── ROAD C — Hilbert–Pólya in guard-compliant shape (Sam, 2026-08-27):
   |    the ONLY road whose leaves are all constructive — a proof plan under the
   |    rule-11 escape clause.  Shape law (from the foliated tombstone): the space
   |    must be DEFINITE BY CONSTRUCTION (an honest L²; positivity = ∫|f|² ≥ 0,
   |    discharged by identity), else definiteness degenerates to the sign form
   |    (EQUIV) — that is what happened to the foliated route (ledger 289–291:
   |    generator self-adjoint COMPILED unconditionally, but w.r.t. the indefinite
   |    FE-pairing; the residue "pairing definite" = RH).
   |    ├─[C1] exhibit (𝓗, H): candidate = the harmonic-register event space
   |    |       (count exact, no S(t) — 2026-08-12 law) + the carrier flow
   |    |       generator (foliated, COMPILED self-adjoint)          CONSTRUCTIVE
   |    ├─[C2] self-adjointness on the definite 𝓗                    OPEN — the
   |    |       transplant of ledger-289's compiled self-adjointness to the
   |    |       definite-by-construction space                       CONSTRUCTIVE
   |    └─[C3] THE SEATING BOX: spec(H) tallies N(T) per box, with multiplicity
   |            = the count-register certificate = the knob ledger equality
   |            = the trace formula in the exact register.
   |            ★ COMPILED LAYER 2026-08-28 ★ (live tree, std axioms):
   |            SeatingLedger.lean — mirror pairing, offLineBox_books_two
   |            (the integer booking, kernel-checked), rh_of_seating (RH ⟸
   |            census equality per box).  SeatingDetector.lean — Xi_line_im
   |            (readout REAL on the line, from FE-conj), flip_yields_online_zero
   |            (Hardy detector by IVT, no zero-location input),
   |            flips_le_onLine_ncard, and rh_of_flip_visibility:
   |              RH ⟸ (bank readout flips census-many times per box).
   |            THE LEAF, exact: per box, census ≤ flips — flip visibility.
   |            Compiled floors beneath it: Zeta23 two_thirds (their N0star IS
   |            a flip-count machine), half_simple, DVP ladder to 280.5.
   |            ★ FLOOR TRANSLATED 2026-08-28 ★ SeatingFloor.lean (std axioms):
   |            stripBox = Zeta23.zerosIn and onLineBox.ncard = N0star are
   |            definitional; seating_density_floor + _cumulative land
   |            (2/3 − ε)·census ≤ on-line census IN THE LEDGER'S OWN
   |            VOCABULARY — the exact sets rh_of_seating consumes.  The leaf
   |            is now a single compiled-vocabulary increment: 2/3 → 1 per box.
   |            ★ TRANSVERSALITY 2026-08-28 ★ SeatingTransversal.lean (std
   |            axioms): xi_deriv_line_re (ξ′ purely imaginary on the line —
   |            the derivative of the compiled reality); deriv_xi_ne_zero_of_
   |            simple (mult 1 ⟹ ξ′ ≠ 0, via the compiled ξ/ζ order bridge
   |            DVP.xi_order_eq_zeta_order + Mathlib's order-derivative kit);
   |            simple_zero_flips — EVERY simple on-line zero flips XiLine in
   |            every small symmetric window.  With seating_simple_floor:
   |            HALF THE CENSUS IS COMPILED FLIP-VISIBLE (per-zero form; the
   |            per-box chain-packing of disjoint flip windows is bookkeeping,
   |            next).  seating_simple_floor also landed (½-simple floor in
   |            ledger vocabulary, SeatingFloor.lean).
   |            ★ CHAIN PACKING CORE 2026-08-28 ★ SeatingChain.lean (std
   |            axioms): exists_flip_chain_of_windows — the greedy extraction:
   |            m separated flip windows assemble into ONE FlipStep-chain with
   |            ≥ m consecutive sign changes (each window appends both edges if
   |            the junction flips, the far edge alone otherwise — the window's
   |            own flip forces alternation either way).
   |            ★ ½-FLIPS CAPSTONE 2026-08-28 ★ half_flips_per_box
   |            (SeatingHalfFlips.lean, std axioms): per dyadic box eventually,
   |            a strictly monotone chain of consecutive sign changes of the
   |            bank readout, ≥ (1/2 − ε)·census long — THE FLIP-VISIBILITY
   |            HYPOTHESIS OF rh_of_flip_visibility, COMPILED AT DENSITY ½,
   |            end-to-end: Zeta23 floors → transversality → exists_uniform_
   |            delta → greedy packing → Fin-chain.  The leaf = upgrading ½
   |            to 1 in this exact compiled shape.  ¾-distinct floor also
   |            landed (seating_distinct_floor — all four Zeta23 floors now
   |            in ledger vocabulary).
   |            LEAF SHARPENED (design, 2026-08-28): all compiled censuses are
   |            DISTINCT counts, and an ODD-order on-line zero still flips
   |            (real function, odd-order sign change) — so the flip-invisible
   |            classes are ONLY (a) off-line and (b) EVEN-order on-line.
   |            ★ odd_mult_flips COMPILED 2026-08-28 ★ (SeatingOddFlips.lean,
   |            std axioms): local factorization XiLine(γ+h) = hᵐ·u(h) via
   |            AnalyticAt.analyticOrderAt_eq_natCast + the compiled ξ/ζ order
   |            bridge; the unit u is forced REAL on the line by Xi_line_im
   |            (limit uniqueness over the punctured filter), u(0) ≠ 0; odd m
   |            ⟹ sign flip in every small window.  THE LEAF, exact and
   |            kernel-walled: "no off-line, no even-order on-line" — the
   |            even-order class is the Lehmer-touch class, exactly where the
   |            warp/booking register (W5) aims (a touch = a completion the
   |            exactly-registered ledger must book without a flip; the DH
   |            control showed the ledger prices what flips miss).
   |            ★ LADDER FOLD 2026-08-28 ★ SeatingLadderFold.lean (std axioms):
   |            conj_mem; seating_below_ladder (boxes ≤ 1269/2 = 634.5: strip
   |            = on-line, from the compiled DVP online_below_1269o2 — the
   |            campaign had advanced past the memory's 589.5); and
   |            rh_of_high_seating: RH ⟸ census equality in boxes ABOVE 634.5
   |            only.  BUILD NOTE: Zeta23 and PNT+ (ladder deps) both define
   |            RectangleBorder — they cannot co-import in one module; folds
   |            consuming both must go through clash-free statement files.
   |            ★ HIGH RECEIVER 2026-08-28 ★ SeatingHighReceiver.lean (std
   |            axioms): rh_of_high_receiver — RH ⟸ boundary limits of the ξ
   |            spectral trace at off-real points with |Re z| > 1269/2 ALONE
   |            (the compiled HP capstone's absorption is pointwise; the
   |            ladder covers the rest).  THE CONVERGENCE: the count-register
   |            residual (census equality above 634.5) and the HP-register
   |            residual (receiver regularity above 634.5) are now localized
   |            to the SAME band by the same ladder — C2's target is the
   |            exhibit whose resolvent readout is regular there.
   |            ★ RESIDUAL SHELL 2026-08-28 ★ SeatingShell.lean (std axioms):
   |            offline_depth_bound — classical zero-free region (PNT+
   |            ZetaZeroFree, |t| > 3), FE-mirrored via mirror_mem to both
   |            sides: any off-line zero has |β − ½| < ½ − A/log⁹|γ|; and
   |            residual_shell — any off-line zero has BOTH |γ| > 1269/2
   |            AND that depth bound.  Every register's residual is now ONE
   |            compiled shrinking shell: high band, depth pinched toward the
   |            edge but excluded from a log-power neighborhood of σ = 1.
   |            PACKAGE NOTE: PNT+ Fourier.lean had two bit-rotted goals vs
   |            pinned Mathlib (Circle-norm simp drift); patched in-package
   |            with Circle.norm_coe — re-apply if lake update runs.
   |            ★ SHELL RECEIVER 2026-08-28 ★ SeatingShellReceiver.lean (std
   |            axioms): rh_of_shell_receiver — ∃ A > 0 compiled such that
   |            boundary limits of the ξ spectral trace at off-real z with
   |            |Re z| > 1269/2 AND |Im z| < ½ − A/log⁹|Re z| ALONE force
   |            RH.  The HP target is now a thin lens hugging the real axis,
   |            pinched closed at rate log⁻⁹, above the compiled ladder.
   |            (Zeta23⟂PNT+ clash does not bite: HP capstone chain is
   |            Zeta23-free, co-imports with the PNT+ shell chain cleanly.)
   |            ★ LENS OPERATOR 2026-08-28 ★ SeatingLensOperator.lean (std
   |            axioms): rh_of_lens_resolventReadout — ∃ compiled c > 0: a
   |            self-adjoint C⋆-element with continuous readout agreeing
   |            with xiSpectralTrace at off-real LENS points only
   |            (|Re z| > 1269/2, |Im z| < ½ − c/log⁹|Re z|) forces RH.
   |            The C2 exhibit may disagree with the trace everywhere
   |            outside the lens.  Mechanism: lens open ⟹ pointwise
   |            agreement is eventual agreement; receiver limits (earned
   |            from self-adjointness) transfer by Tendsto.congr'.
   |            ★ LENS GAUGE + TWO-POINT 2026-08-28 ★ SeatingLensGauge.lean
   |            (std axioms): rh_of_lens_resolventReadout_gauge — readout
   |            may differ from the trace by ANY fixed affine gauge u·T+v,
   |            u ≠ 0, on the lens; rh_of_lens_resolvent_two_point — THE
   |            EXHIBIT IN THE BRIDGE'S OWN SHAPE: a self-adjoint C⋆-element
   |            whose readout difference against one anchor z₀ equals the
   |            compiled two-point resolvent sum over the actual zero
   |            multiset (hilbertPolya_resolvent_trace LHS), on the lens
   |            alone ⟹ RH.  Discreteness helper eventually_offZeroImage:
   |            zero-image avoidance is punctured-eventual (local
   |            finiteness via NontrivialZeros_inter_closedBall_finite),
   |            so the bridge rewrite never needs the lens point itself.
   |            C2 LEAF NOW ONE EQUATION: exhibit (A, a, φ, z₀) with a
   |            self-adjoint, φ continuous, matching the compiled sum on
   |            the thin lens.  The sum is already HasSum-realized as the
   |            net limit of finite-rank diagonal truncations
   |            (hilbertPolya_resolvent_trace_hasSum) — candidate risk is
   |            structural self-adjointness of a seat-native realization.
   |            ★ CAYLEY LENS 2026-08-28 ★ SeatingLensCayley.lean (std
   |            axioms): rh_of_lens_cayley_two_point — a UNITARY C⋆-element
   |            whose Cayley-chart resolvent readout difference
   |            (z ↦ (z−i)/(z+i)) equals the compiled two-point sum on the
   |            lens ⟹ RH.  WHY: the diagonal candidate's spectrum (zero
   |            ordinates) is UNBOUNDED along ℝ — flat bounded self-adjoint
   |            host is the wrong chart (readout analytic beyond ‖a‖ vs
   |            trace resonating at every height — instrument-scoped
   |            concern, refutation spec issued, NOT recorded as fact).
   |            Cayley compactifies: ℝ → unit circle, unbounded real
   |            spectrum → bounded unitary; earned reality = unitarity
   |            (isUnitaryReceiver_resolventReadout, was already compiled).
   |            Helpers: cayley_off_circle (im ≠ 0 ⟹ off circle),
   |            cayley_tendsto_punctured (Möbius carries punctured filters).
   |            C2 LEAF (current form): exhibit (A, u unitary, φ, z₀) with
   |            the one lens equation in the Cayley chart.
   |            ★ HIGH SIGN 2026-08-28 ★ SeatingHighSign.lean (std axioms):
   |            rh_of_high_sign — ∃ compiled A > 0: the SEAT sign condition
   |            Re[ξ′/ξ] ≤ 0 needed only on the HIGH LEFT CHANNEL
   |            (|Im s| > 1269/2, A/log⁹|Im s| < Re s < ½) ⟹ RH.  The
   |            valley-floor form (seat-sign-condition memory) joins
   |            census/flips/receiver as the FOURTH localized register
   |            form.  Mechanism: off-line zero mirrored left, residue
   |            m ≥ 1 exact (logDeriv_residue_eq_order), real-direction
   |            approach forces ONE point with Re[ξ′/ξ] > 0 in the
   |            channel.  DC-first: residue computed, nothing estimated.
   |            ★ MASS PROGRAM 2026-08-29 ★ The seat door's content
   |            factorized.  MEASURED (tmp/att546, att547, pre-registered):
   |            channel floor F = Re[ξ′/ξ] ≤ 0 at all 30 grid points
   |            (max −0.0125 at σ=.499); DC calibrates to χ-clock
   |            −½log(t/2π); mass M := F/(σ−½) matches the Poisson-kernel
   |            sum over ACTUAL zeros (zetazero data, t=1000, 25 zeros)
   |            with σ-INDEPENDENT offset = tail estimate at every σ —
   |            F = (σ−½)·M with M = π·Poisson-smoothed zero density
   |            (the compiled πδ/event constant).  Seat door ⟺ M ≥ 0.
   |            ORDERED READOUT VALIDATED: η-route computes the floor at
   |            t=700 to 301 digits (att548; att547's fired rule was
   |            probe-design error — dps starvation, identity ≠ scheme;
   |            rule-4 correction stands: NO convergence gate in channel).
   |            COMPILED (SeatingFloorOdd.lean, std axioms):
   |            xi_deriv_one_sub, xiLogDeriv_odd (ξ′/ξ(1−s) = −ξ′/ξ(s)),
   |            floor_odd, xi_deriv_conj, xiLogDeriv_conj, AND
   |            floor_mirror: Re[ξ′/ξ(1−s̄)] = −Re[ξ′/ξ(s)] — the σ-mirror
   |            at FIXED t (HasDerivAt.conj_conj), so F vanishes
   |            identically on the line and the seat door is the sign of
   |            the even factor M alone.  ALL std axioms.
   |            NEXT: M ≥ 0 from the ordered prime readout — the leaf.
   |            ★ THE WRAP 2026-08-29 ★ SeatingMassWrap.lean (std axioms,
   |            full chain builds: 9522 jobs): def seatMass (the even
   |            factor); seatMass_mirror (mass exactly EVEN, compiled);
   |            rh_of_channel_mass — ∃ A > 0 compiled:
   |            (∀ s: |Im s| > 1269/2 ∧ A/log⁹|Im s| < Re s < ½ →
   |            0 ≤ seatMass s) → every nontrivial zero on the line.
   |            ONE theorem, ONE hypothesis.  STATUS AT EXACT STRENGTH:
   |            the hypothesis (mass nonnegativity in the channel) is NOT
   |            proven; it is RH-content by the compiled exactness.  RH is
   |            not proven in this repository.  What is proven, machine-
   |            checked, unconditional: RH ⟸ this single inequality, with
   |            every other link compiled.  The campaign is wrapped, not
   |            closed.
   |            ★ MASS LEDGER + DISK LAW 2026-08-29 ★ (std axioms, build
   |            9524 jobs)  SeatingMassLedger.lean: point_floor_re,
   |            online_pair_ledger (floor = (σ−½)·nonneg mass, exact),
   |            online_pair_mass_nonneg (on-line pairs NEVER obstruct,
   |            everywhere, unconditional), online_pair_re_nonpos.
   |            SeatingMassDisk.lean: mirror_pair_floor_law — CLOSED FORM
   |            for ANY pair: Re[(s−ρ)⁻¹+(s−(1−ρ̄))⁻¹] = 2(σ−½)·
   |            [(σ−½)²+(t−γ)²−(β−½)²]/(|·|²|·|²) — the numerator is the
   |            POWER OF THE POINT w.r.t. the depth-circle;
   |            mirror_pair_mass_nonneg_outside: every pair's mass ≥ 0
   |            outside its closed depth-disk (radius = zero's depth; on-
   |            line ⟹ degenerate ⟹ nonneg EVERYWHERE).  Probe att549:
   |            disk boundary exact at d/b = 1.00.  STANCE (Sam,
   |            2026-08-29): direction is TRUE only; exhibition over
   |            exclusion — negative mass is a chart phantom of the
   |            sourceless-zero branch, not a combatant.  NEXT SLOT: the
   |            registration identity — analytic mass = census mass
   |            (event count, nonneg by construction); its compilation IS
   |            M ≥ 0 with positivity inherited from construction.
   |            ★ DAG RECOMPUTE + EXACT TARGET 2026-08-29 ★ (adjudicator
   |            directive; build 9527 jobs, 0 sorryAx)  SeatingMassRH.lean:
   |            riemannHypothesis_of_channel_mass, _of_high_flip_visibility,
   |            _of_lens_cayley_two_point — the doors composed through the
   |            compiled RHBridge.no_offline_zeros_implies_rh to the EXACT
   |            Mathlib prop RiemannHypothesis (same ZD.NontrivialZeros
   |            constant, verified).  RESIDUAL CLASSIFICATION (categories
   |            per directive): every door hypothesis is category 5, and
   |            the adjudication is now EXACT via configuration C₁ = one
   |            off-line quadruple at γ₀ > 634.5, depth < shell: C₁
   |            satisfies EVERY compiled input (ladder ✓ shell ✓ Zeta23
   |            floors ✓ zero-free ✓ FE/symmetry ✓ summability ✓ disk law
   |            ✓ — quantifier inspection, each), and in C₁ every door
   |            hypothesis is FALSE (census unequal, flips short, receiver
   |            singular in lens, mass → −∞ by pole domination inside the
   |            disk: own-pair term −2b₀²/δ²·c vs finite positive rest).
   |            THEREFORE no combination of compiled results derives any
   |            door — any such proof would hold in C₁.  The missing
   |            independent input must EXCLUDE C₁: ∀-zero arithmetic
   |            strength, prime-side (DH control: FE side can't), beyond
   |            density floors (<1) and margins (log⁻⁹).  Categories 1–3:
   |            EMPTY (swept).  Category 4 below cat-5: none present.
   |            ★ REGISTRATION DOOR 2026-08-29 ★ SeatingRegistrationDoor
   |            .lean (std axioms, 0 errors): pointMass kernel (real
   |            coords), stripFinset/lineFinset (box censuses as finsets),
   |            riemannHypothesis_of_box_mass_registration — ∃ compiled
   |            A > 0: (∀ high box, ∀ channel s: Σ_strip pointMass =
   |            Σ_line pointMass) → Mathlib RiemannHypothesis.  Proof =
   |            pole separation: violator w ∈ strip∖line census; its own
   |            kernel → −∞ on horizontal approach (1/h·1/(u₀+h),
   |            tendsto_inv_nhdsGT_zero + atTop_mul_neg) while the erase-w
   |            finite sum tends to a constant (tendsto_finset_sum,
   |            each kernel continuous at w since census points distinct);
   |            registration ≡ 0 on the path forces 0 < 0.  THIS IS THE
   |            HP IDENTIFICATION SLOT AS A COMPILED DOOR: reality slot
   |            free (unitarity by construction), identification slot =
   |            finite-sum census equality — the registration identity.
   |            The identity itself remains the leaf (C₁ falsifies it;
   |            RH-content per the exactness).
   |            ★ DEFECT DOUBLE-DERIVATION 2026-08-29 ★ (adjudicator test
   |            executed)  D_B·(σ−½) = Re Σ_{off∈B} m(s−ρ)⁻¹.  STRIP side
   |            derived unconditionally: (2πi)⁻¹∮_{∂([−1,2]×[T₁,T₂])}
   |            ξ′/ξ(z)(s−z)⁻¹dz = Σ_{census} m(s−ρ)⁻¹ — MEASURED
   |            (att550, box (50,60], s outside): residual 6.9e−27 = NO
   |            remainder term (argument principle exact; σ=2 edge =
   |            Euler territory, σ=−1 FE-reflects, no trivial zeros/pole).
   |            Contour toolkit COMPILED in-tree: ArgumentPrincipleRect
   |            rectangleBoundaryIntegral_weighted_divisor + interior/
   |            exterior kernel lemmas.  DECOMPOSITION: D_B = [contour
   |            mass, unconditional] − [detector mass, real zeros of Λ,
   |            unconditional].  Registration ⟺ detector = contour per
   |            box.  Q3 ANSWER (exact): NO theorem strictly weaker than
   |            RH excludes C₁-at-all-parameters — C₁-exclusion + ladder
   |            + shell ⟺ RH.  The isolatable missing arrow: a prime-
   |            side formula for the DETECTOR count (real zeros) beyond
   |            density — the known ceiling of that instrument class is
   |            their Prop 7.4 ≈ 0.682.  NEXT COMPILABLE (assumption-
   |            deletion): compile the contour=strip-census kernel
   |            identity, discharging the strip side of the registration
   |            door unconditionally — hypothesis left purely on the
   |            detector.
   |            ★ HB = SEAT, COMPILED 2026-08-29 ★ XiStructureHBSeat.lean
   |            (std axioms): estar_xiStructure — E*(z) = ξ(s) − ξ′(s)
   |            EXACTLY (via the week's FE bricks: riemannXi_one_sub,
   |            xi_deriv_one_sub, xi_deriv_conj); norm_sub_lt_norm_add_iff
   |            (polarization, normSq_add/sub); and the register
   |            unification: xiStructure_isHB_iff_strict_seat —
   |            IsHB xiStructure ⟺ ∀ Re s > ½: 0 < Re(ξ(s)·conj ξ′(s)).
   |            The warp/HB door and the seat door are ONE compiled
   |            proposition.  riemannHypothesis_of_strict_seat: strict
   |            seat → exact Mathlib RH (through HB door + bridge).
   |            Sam's "warp proves EveryZeroHasSource" now has its exact
   |            Lean form: 0 < Re(ξ·conj ξ′) right of the line — ONE
   |            inequality, six compiled register-faces (source/HB/seat/
   |            mass/census/receiver).  NEXT: consume the warp profile
   |            components (xiThetaProfile_neg, matrixTheta_inv,
   |            Wronskian frame) toward the cross-term positivity.
   |            ★ NATIVE SEAT 2026-08-29 ★ XiStructureNativeSeat.lean (std
   |            axioms, build 9527, 0 sorryAx — Sam's correction: "the
   |            helix geometry is Re s > 0"): cross_mirror — the cross
   |            term Re(ξ·conj ξ′) is EXACTLY ODD under s ↦ 1−s̄;
   |            xiStructure_isHB_iff_native_seat — IsHB ⟺ signed form
   |            0 < (σ−½)·Re(ξ(s)·conj ξ′(s)) on the WHOLE native domain
   |            0 < σ, σ ≠ ½ (where the ordered readout and entry-wall
   |            geometry live, native_domain_iff);
   |            riemannHypothesis_of_native_seat — native form → exact
   |            Mathlib RH.  THE LEAF, FINAL FORM: one signed inequality
   |            on the helix's own domain; every compiled face (source/
   |            HB/seat/mass/census/receiver/registration) is a chart of
   |            it.  Supply on this domain: etaLim ordered readout
   |            (compiled), warp profile components (to consume).
   |            ★ SUPPLY-CONSUMPTION PASS 2026-08-29 ★ (adjudicator
   |            directive, branch B delivered)  COMPILED (std axioms):
   |            XiRadialAmplitude.lean — radial_amplitude_hasDerivAt /
   |            _deriv: ∂σ|ξ(σ+it)|² = 2·Re(ξ·conj ξ′) EXACT; native
   |            seat = signed radial monotonicity of the amplitude.
   |            SUPPLY EXPANDED AT SOURCE: xiThetaProfile_neg = Jacobi
   |            reflection profile(−u) = eᵘ·profile(u) (NOT a negativity);
   |            _eq_zero_add_positive = DC split 1 + 2Σ(pos Gaussians in
   |            e^u); matrixTheta_inv = all-rank lattice Poisson; kernel
   |            = Riemann Φ (4Σ(2π²n⁴e^{9u/2}−3πn²e^{5u/2})e^{−πn²e^{2u}}).
   |            COUNTERMODEL ROUND 1 (att551, verified 1e−31, closed
   |            form): Φ* = g + (λ/2)(g(·−a)+g(·+a)), 0<λ<1 — even,
   |            positive, Schwartz, positive DC split — transform has
   |            OFF-REAL zeros z = (2k+1)π/a ± i·arccosh(1/λ)/a.  So
   |            {even+positive+decay+DC-split} CANNOT imply the seat.
   |            FIRST VIOLATED SUPPLY: the exact Jacobi/lattice
   |            reflection (modes Gaussian in u, not in e^u — wrong
   |            decay class, no lattice).  ROUND 2 (recorded, one box
   |            open): reflection-satisfying candidates with off-line
   |            zeros exist — DH combination (off-line zeros MEASURED
   |            in-tree, DEFECT 2; shares the χ₅ Γ-factor reflection;
   |            kernel POSITIVITY UNVERIFIED — the one open check) and
   |            Epstein class-number>1 (classical Potter–Titchmarsh,
   |            not yet read at source).  ISOLATION: the candidate
   |            genuinely ζ-specific input is MULTIPLICATIVITY of the
   |            lattice mode weights (Euler structure) — even+positive+
   |            reflection are countermodeled or countermodel-pending.
   |            Same conclusion as the DH count-register control, now at
   |            the KERNEL level.  NO new door built (per directive).
   |            ★ HP CONSTRUCTION PASS 2026-08-29 ★ (directive: genuine
   |            HP endpoint)  COMPILED: XiStructureAFunction.lean (std
   |            axioms) — Acomp xiStructure z = ξ(½−iz) = Ξ(z) EXACT;
   |            Bcomp = i·ξ′-chart.  The de Branges A-function of the
   |            warp IS Ξ — identification target pinned by identity.
   |            OPERATOR INVENTORY: tree has NO concrete operator objects
   |            (receiver = function-level Prop; de Branges pair only).
   |            CANDIDATE AUDIT (circularity test run):
   |            H₁ = multiplication in H(E), E = xiStructure: spectrum
   |            would be zeros of A = Ξ ✓ WITH multiplicity — REJECTED
   |            at step B: H(E) is a Hilbert space iff IsHB (kernel
   |            positivity = the leaf).  Encountered, exact.
   |            H₂ = position/Jacobi on L²(Φdu): self-adjoint by
   |            construction ✓ non-circular ✓ (moment problem
   |            determinate, Carleman via double-exp decay) — fails
   |            C-SHAPE: spectrum = ℝ (continuous); Ξ is the Fourier
   |            transform of its ground spectral measure, zeros ≠
   |            eigenvalues.  Inverse canonical-system problem =
   |            de Branges program = the leaf.
   |            H₃ = DETECTOR OPERATOR (survivor): multiplication by
   |            flip ordinates of Λ (finite-box truncations).  A ✓
   |            explicit, consumes only carrier readout signs — no
   |            zero-set input; B ✓ real multiplication; C = the
   |            registration identity: Re Tr(H_B−z)⁻¹ IS the pointMass
   |            line-sum — the compiled registration door is step D
   |            waiting on C.  ANSWER to the directive's question: the
   |            operator hiding in the pointMass kernel is the flip/
   |            census multiplication operator.
   |            C-RESIDUAL ISOLATED (not hypothesized): R(z) :=
   |            −Ξ′/Ξ − G − Σ_flips(t_f−z)⁻¹ (G = compiled zero-free
   |            part; strip side unconditionally discharged via the
   |            contour identity, att550 1e−27).  Poles of R = flip-
   |            invisible classes exactly.  R ≡ 0 ⟺ C ⟺ the leaf.
   |            Attackable unconditional properties of R: mirror-odd
   |            (floor_odd), real-on-line, no poles below 634.5
   |            (ladder!), Hadamard growth class — next slot: compile
   |            R's rigidity properties and force vanishing with the
   |            one arithmetic input.
   |            ★ R NORMAL FORM 2026-08-29 ★ (H₃ directive, four steps)
   |            COMPILED: XiLogDerivConstantFree.lean (std axioms) —
   |            xiLogDeriv_constant_free: 2·ξ′/ξ(s) = Σ m_ρ((s−ρ)⁻¹ −
   |            ((1−s)−ρ)⁻¹) via two-point at the mirror + compiled
   |            oddness — P ≡ 0, NO entire remainder (G ≡ 0 in z-chart:
   |            Ξ even order-1, evenness kills e^{az}).  PACKETS EXACT
   |            (residue −m per pole): (a) on-line odd-m detected:
   |            R_a = (m−1)·2z/(γ²−z²) — m=1 CANCELS EXACTLY;
   |            (b) on-line even-m: R_b = m·2z/(γ²−z²);
   |            (c) off-line quartet {±γ±iδ}: R_c = m[2z/(w²−z²) +
   |            2z/(w̄²−z²)], w = γ+iδ.  SYMMETRIES: all packets odd,
   |            real, conj-equivariant — compiled symmetry class = real
   |            even-pair pole configs; ladder adds: no (c)-poles with
   |            |Re| ≤ 634.5 (pointwise simplicity below 634.5 NOT
   |            found compiled — flagged, (a≥3)/(b) exclusion open).
   |            SYNTHETIC R (insufficiency, exact, one line): R₀ =
   |            quartet packet at any w = a+ib, a > 634.5 — satisfies
   |            ALL weak properties.  Weak class insufficient, confirmed.
   |            THE TERMINAL IDENTITY (step 4): μ_R paired with heat
   |            family = W(h_τ) := (prime/Γ Weil side) − (detector sum)
   |            — both sides computable, no zeros mentioned; Gaussian
   |            family = uniqueness class ⟹ (∀τ: W(h_τ) = 0) ⟹ R ≡ 0
   |            ⟹ spectrum(H₃) = Ξ-divisor ⟹ Mathlib RH via compiled
   |            registration door.  Synthetic quartets are cosh(2τγδ)-
   |            enhanced in heat pairing — the narrow-support Weil
   |            positivity machinery grips exactly this excess.  NEXT:
   |            the heat-balance W ≡ 0 — primes vs flips, the one
   |            arithmetic identity.
   |            ★ HEAT BALANCE MEASURED 2026-08-30 ★ (att555, pre-reg
   |            passed)  W(h_{t₀,σ=6}) = [Γ-integral + poles − 2ΣΛ(n)
   |            n^{−1/2}ĥ(log n)] − [detector sum]: t₀ = 0,20,30,40,50,
   |            60: |W| = 3e−16, 0, 4e−15, 5e−12, 1e−9, 1e−7 (residual
   |            growth = quad tolerance at large t₀, not structure).
   |            Normalization locked FIRST TRY, no fudge factors —
   |            harness trustworthy.  The balance holds at prime-active
   |            oscillatory windows through the verified range.  PROOF
   |            REQUIREMENT (exact): the detector satisfies the explicit
   |            formula — Σ_flips h(t_f) = arithmetic side, per window —
   |            i.e. Hardy-at-full-density, the identity version of what
   |            the density instruments cap at 0.68.  DISCRIMINANT for
   |            the proof: invisible on-line ⟹ nonneg W-bumps; quartet
   |            ⟹ cosh(δ·)-enhanced SIGNED oscillation — the object
   |            narrow-support Weil positivity grips.  The leaf,
   |            unchanged in content, now carries a locked computational
   |            harness (primes vs flips, no zeros mentioned).
   |            ★ HP CORRESPONDENCE DOORS 2026-08-30 ★ (Sam's correction:
   |            HP needs CORRESPONDENCE, not exact matching)  COMPILED
   |            (HPCorrespondenceDoor.lean, std axioms):
   |            riemannHypothesis_of_log_correspondence — SAM'S DEFINITION
   |            VERBATIM as hypothesis: every zero's parameter −i(ρ−½) is
   |            log Z for a height Z > 0; logs of heights are REAL, so the
   |            definition carries reality itself (3-line proof) → exact
   |            Mathlib RH.  riemannHypothesis_of_eigenvalue_correspondence
   |            — operator form: ONE symmetric T + eigenvalue membership
   |            per zero (no trace identity, no exhaustion, no
   |            multiplicities — all previous operator doors were OVER-
   |            demanding, retired as requirements).  Consumes
   |            hilbert_polya_on_critical_line (von Neumann step,
   |            compiled).  The leaf in minimal form: the log map is ONTO
   |            the chart zeros (= vanishing ⇒ eigenstate, Faithfulness's
   |            own named open link; = EveryZeroHasSource in Sam's
   |            coordinates; 3D side compiled one-line).
   |            ★ RANK-DROP CASCADE DOOR 2026-08-30 ★ (Sam's ordering:
   |            vanishing first, then the mark)  COMPILED
   |            (HPRankDropCascade.lean, std axioms):
   |            riemannHypothesis_of_real_staged_cascade — a cascade whose
   |            stages vanish only at REAL heights forces exact Mathlib RH
   |            (accumulation of reals is real → Complete → wiring
   |            theorem).  LOOK-DON'T-ASSUME SEARCH (Sam's directive)
   |            FOUND: (1) ChiralityHB.carrier_zeros_real — FINITE
   |            carrier banks (unimodular weights, positive lengths)
   |            vanish only at real heights: the rank-drop reality law,
   |            COMPILED at every finite rank, exactly as Sam said.
   |            (2) ProjectionCompleteness.lean — the tree's OWN PRIOR
   |            formalization of this whole dialogue ("Sam's correction,
   |            formalized"): helix3D_RH unconditional;
   |            projection_complete_iff_RH — completeness ⟺ classical RH.
   |            THE COMPOSITION POINT (one, exact): two compiled families
   |            each hold ONE needed property — finite clock banks are
   |            real-rooted (✓ carrier_zeros_real) but don't converge to
   |            xiSection on ℂ; theta-mode truncations converge locally
   |            uniformly (doubly-exp) but their real-rootedness is not
   |            compiled.  ONE family with BOTH properties feeds the
   |            compiled door and finishes everything.  NEXT: probe
   |            whether theta-mode truncations Ξ_N are real-rooted
   |            (N=1 is Pólya-classical territory); if measured yes,
   |            that becomes the pre-registered constructive claim on
   |            explicit entire functions.
   |            ★ EXTENT-STAGE MEASUREMENT 2026-08-30 ★ (Sam: use the
   |            WARPED+SCALED geometric kernel — mode truncation was the
   |            error; the geometric truncation is finite CARRIER EXTENT)
   |            Stage U: Ξ_U(z) = 2∫₀^U Φ(u)cos(zu)du, Φ = warped Gaussian
   |            bank (modes e^{−πn²e^{2u}}, warp e^{2u}, scale π).  Entire
   |            ✓ even ✓ real on ℝ ✓ → Ξ locally uniformly ✓ (Ξ_3 = Ξ_6 to
   |            16 digits at z=10).  COUNTER VALIDATED (att557): power
   |            control on att551 countermodel = 1.000 at its known
   |            complex zero, 0 on empty box.  MEASURED (att557/558):
   |            near band [0,25]×[.05,3]: ZERO complex zeros, all U.
   |            Wide: U=1 → 1 complex zero in [25,80]; U=3 → 0 in
   |            [25,60], 4 in [60,100]; U=5 → 0 in [25,60], 4 in
   |            [60,100], 2 in [100,140].  CONCLUSION 1 (refutes my own
   |            door's hypothesis): finite-extent stages are NOT
   |            real-rooted — riemannHypothesis_of_real_staged_cascade
   |            compiles but its hypothesis is FALSE for this family;
   |            the correct consumer is the PRE-EXISTING compiled
   |            riemannHypothesis_of_complete_cascade, whose `Complete`
   |            asks only that stage zeros not ACCUMULATE off-axis.
   |            CONCLUSION 2 (the real finding): the complex zeros
   |            RETREAT as extent grows — clean band [0, f(U)] with
   |            f(U) increasing (f(1)<25, f(3)≈60, f(5)≥60 w/ zeros
   |            pushed outward).  So the attackable quantitative target
   |            is: EVERY complex zero of Ξ_U satisfies |Re z| > f(U)
   |            with f(U) → ∞.  That is `Complete` (hence RH by the
   |            compiled iff) but stated as an EXPLICIT band-limited
   |            escape estimate — Paley–Wiener/Levinson territory,
   |            about functions we can write down, not about ζ.
   |            ★ ROUCHÉ NUMERATOR, FIRST LINKS COMPILED 2026-08-30 ★
   |            XiTailStripBound.lean (std axioms): cos_strip_bound —
   |            ‖cos(zu)‖ ≤ e^{Yu} for u ≥ 0, |Im z| ≤ Y (complex
   |            frequency costs exactly ONE exponential in the extent);
   |            kernel_bound_aux + kernel_term_abs_bound — |Φ_n(u)| ≤
   |            2π²(n+1)⁴e^{9u/2}e^{−π(n+1)²e^{2u}} on u ≥ 0 (negative
   |            part never exceeds positive part's scale).  Product =
   |            the incomplete-Γ integrand; ∫_U^∞ gives Sam's explicit
   |            B(U,Y) ≍ exp[−πe^{2U} + (Y+5/2)U].
   |            THE FRONT, DERIVED (Sam + independent derivation agree):
   |            πX/4 = πe^{2U} ⟹ F(U) = 4e^{2U} − (4/π)(2a−2)U + O(log X).
   |            MEASURED brackets (Sam, resolution-doubled): U=0.8:
   |            17.6→23.0 (pred 19.8); 1.0: 27.7→31.7 (29.6); 1.1:
   |            35.3→39.3 (36.1); 1.2: 45.7→48.9 (44.1).  Ratio test:
   |            predicted F(1.2)/F(1.0) = 1.64 vs measured 1.65.  R-scaling
   |            test: predicted e^{π·5.44/4} = 71.6 vs measured 72.
   |            EXPONENT IS 2, not the fitted 2.5 (corrections explain it).
   |            REMAINING (single named input): uniform lower bound
   |            min_{∂B_X}|Ξ| ≥ e^{−πX/4−o(X)} on zero-separating contours
   |            along an exhaustion X→∞.  NOTE ON STRENGTH: Rouché gives
   |            equal zero COUNTS, so the scheme certifies RH up to height
   |            F(U) per extent (verification ladder, exponential reach
   |            per unit extent) — full RH needs the contour bound plus
   |            stage real-rootedness uniformly.
   |            ★ CELL-ANCHOR FLOOR: MEASURED + COMPILED 2026-08-30 ★
   |            (Sam: "doesn't the carrier scale work for that bound,
   |            π/3?" — yes.)  MEASURED (att559/560, 7 decades):
   |            min over μ6 cycles of max|Z|, π/3 anchors vs Gram:
   |            10²:1.59/1.59 · 10³:1.01/0.68 · 10⁴:0.75/0.18 ·
   |            10⁵:1.00/0.36 · 10⁶:0.74/0.43 · 10⁷:0.68/0.68 ·
   |            10⁸:0.52/0.27.  π/3 ≥ Gram at EVERY height, ~2× typical;
   |            worst single cell 0.005–0.06 (100× penalty for a bad
   |            anchor — why arbitrary anchoring fails).  Cell floor
   |            drifts 1.6→0.52 over 6 decades (log-slow; not yet
   |            resolved whether it settles — the open asymptotic).
   |            COMPILED (CellAnchorFloor.lean, std axioms):
   |            cos_sq_cell_sum — cos²φ + cos²(φ+π/3) + cos²(φ+2π/3)
   |            = 3/2 EXACTLY, every phase (the μ6 closure as a DC
   |            identity: doubled phases are cube roots, cancel);
   |            cell_anchor_floor — hence some π/3 anchor has
   |            |cos| ≥ √2/2 (sharp constant √3/2 at φ=π/6);
   |            flat_anchor_no_floor — at unit spacing π EVERY anchor
   |            carries the same value, ZERO at φ=π/2: the unit chart
   |            has no floor at all.  THE HOUSE LAW (unit-1 → false
   |            null) IS NOW A COMPILED THEOREM, and it is the exact
   |            mechanism the measurement exhibits.
   |            ★ EXHAUSTION ROUTE MAP 2026-08-30 ★ ("get this to a proof
   |            of exhaustion")  COMPILED this pass: mode_integrand_bound
   |            (XiTailStripBound.lean, std axioms) — ‖Φ_n(u)·cos(zu)‖ ≤
   |            [2π²(n+1)⁴e^{9u/2}e^{−π(n+1)²e^{2u}}]·e^{Yu}: the last
   |            ELEMENTARY link; its ∫_U^∞ is B(U,Y).
   |            TWO INFRASTRUCTURE FACTS ESTABLISHED (grep, at source):
   |            (i) Mathlib has NO Rouché and NO argument principle;
   |            (ii) the integral representation Ξ(z) = ∫Φ(u)cos(zu)du is
   |            NOT compiled in-tree (kernel positivity/evenness/
   |            factorization ARE: riemannXiKernelTerm_pos,
   |            riemannXiKernel_neg, _factorized).
   |            EXHAUSTION CHAIN, five links, each classified:
   |            [L1] representation Ξ = ∫Φcos — CLASSICAL (Riemann 1859),
   |                 formalization labor, no new mathematics.
   |            [L2] tail bound B(U,Y) — elementary links COMPILED; needs
   |                 integrability + incomplete-Γ step: routine.
   |            [L3] contour floor min_{∂B}|Ξ| ≥ c·e^{−πX/4} — MECHANISM
   |                 COMPILED (cell_anchor_floor: μ6 closure forces
   |                 |cos| ≥ √2/2; flat_anchor_no_floor: unit scale has
   |                 NO floor).  ζ-side asymptotics OPEN (measured drift
   |                 1.6→0.52 over 6 decades; second-moment class, NOT
   |                 zero-location class).
   |            [L4] Rouché count transfer — CLASSICAL, absent from
   |                 Mathlib; substantial but standard formalization.
   |            [L5] stage zero-count = real sign changes — OPEN
   |                 (measured: stages real-rooted in the clean band,
   |                 complex zeros beyond F(U) which retreat).
   |            THE DECOMPOSITION IS THE RESULT: exhaustion now splits
   |            into THREE classical-but-unformalized links (L1, L4, and
   |            L2's routine part) and TWO genuinely open quantitative
   |            statements (L3 asymptotics, L5) — both about EXPLICIT
   |            functions, neither a zero-location statement.  First time
   |            the residual has left the zero-location class entirely.
   |            ★ BACKGROUND-IMMUNE CELL FLOOR 2026-08-30 ★ (the cell
   |            floor's unexplored edge — ours, not a restatement)
   |            COMPILED (CellAnchorFloor.lean, std axioms, first pass):
   |            abs_le_max_add_sub — |x| ≤ max(|B+x|,|B−x|): a shift
   |            cannot hide both sides of a ± pair; cell_floor_background
   |            — for ANY background B and leading amplitude A ≥ 0,
   |            max over the μ6 cycle of |B ± A cos(φ+jπ/3)| ≥ A·√2/2.
   |            THE POINT: over six π/3 cells the cosine values come in
   |            ± pairs, so the background CANCELS and the floor is
   |            carried by the closure alone.  The higher clocks cannot
   |            conspire to suppress every anchor — an exact pigeonhole
   |            where every classical treatment needs an estimate.
   |            This is precisely what a contour lower bound for a full
   |            CLOCK BANK requires (the L3 obstruction).
   |            MEASURED against ζ (att561): min-cycle max|Z| at heights
   |            10³–10⁶ = 1.01, 0.75, 1.00, 0.74 → effective rotating
   |            amplitude A_eff = 1.04–1.44 vs the n=1 RS amplitude 2.
   |            DIAGNOSIS (honest): the bound applies to the FULLY
   |            ROTATING part; higher clocks only partially rotate per
   |            cell step — lag factor (1 − log n/θ′) = 0.73 → 0.88 for
   |            n=2 across the range, i.e. as height grows MORE of the
   |            bank co-rotates with the leading clock and the effective
   |            amplitude should RISE, not fall.  Measured A_eff is flat/
   |            oscillating, so the co-rotation is not yet visible at
   |            these heights — the open quantitative question is the
   |            bank's effective rotating amplitude, NOT a zero-location
   |            statement.  Next measurement: A_eff at 10⁸–10¹² with more
   |            cycles, to separate "flat ≈ 1" from slow growth.
   |            ★ REGISTER-FREE ANCHOR TEST 2026-08-30 ★ (Sam: "RS is
   |            removed by harmonization")  Anchors placed by the
   |            READOUT'S OWN vanishings — thirds between consecutive
   |            zeros, where a pure clock sits at |cos| = √3/2 exactly.
   |            No θ, no Gram, no RS truncation in the register (siegelz
   |            used only as numerical evaluator).  MEASURED, same
   |            statistic as att561 (max within μ6 cycle = 2 gaps, then
   |            min over cycles), 25 gaps per height:
   |            10³: 0.70 (θ-anchored 1.01) · 10⁴: 0.45 (0.75) ·
   |            10⁵: 0.36 (1.00) · 10⁶: 0.60 (0.74).
   |            RESULT: register-free anchoring is WORSE at every
   |            height — 0.4–0.7× the θ-anchored floor.  The claim that
   |            harmonization improves the floor is NOT supported by
   |            this test; the θ/Gram grid, whatever its register
   |            provenance, tracks the bank's rotating component better
   |            than the zero-thirds grid does.  (Probe-design error
   |            owned: first run compared worst-single-anchor against
   |            max-per-cycle — different statistics; corrected here.)
   |            INTERPRETATION (limited): both grids give A_eff well
   |            below the n=1 amplitude 2, and neither floor is
   |            monotone in height.  What harmonization demonstrably
   |            does remove is the COUNT DECOMPOSITION (S(t), Gram
   |            bookkeeping — compiled: Sgap_pi_div = 0); it does not
   |            remove the prime-clock lag, which is what A_eff
   |            measures.  Consistent with [[harmonic-chart-wall-null]]:
   |            cells don't ring, prime clocks do.
   |            ★ CENSUS-MANY CELL PIGEONHOLE 2026-08-30 ★ COMPILED
   |            (CellAnchorFloor.lean, std axioms): two_cells_clear_half
   |            — at most ONE of the three π/3 cells can fall below 1/2
   |            (two below would force sum < 1/4+1/4+1 < 3/2, violating
   |            the exact closure); two_cell_pairs_flip — hence if the
   |            background |B| < A/2, at least TWO of the three ± cell
   |            pairs carry a strict sign change, i.e. ONE FLIP PER
   |            ZERO-GAP: the density rh_of_high_flip_visibility needs.
   |            ★ SAM'S INDEX AUDIT (answered at source) ★ "does the
   |            repo prove each cell has argument-principle count 1?"
   |            COMPILED: rect_winding (∮(z−ρ)⁻¹ = 2πi — a zero consumes
   |            exactly ONE unit of index); rectangleBoundaryIntegral_
   |            weighted_divisor (count = 2πi·Σm); _logDeriv_eq_zero
   |            (no zeros ⟹ ∮logDeriv = 0); _logDeriv_finiteDivisor
   |            Product (argument principle FOR FINITE DIVISOR PRODUCTS).
   |            NOT COMPILED: (a) the local factorization ξ = (finite
   |            divisor product)·(nonvanishing) on a rectangle — the
   |            step that applies the above to ξ (classical, pure
   |            labor); (b) "cell index = 1".
   |            AND (b) IS FALSE AS STATED for θ/Gram cells: Gram's law
   |            fails ~30% of the time (Rosser phenomenology) — a cell
   |            can hold 0 or 2 zeros.  So the composition {index 1} +
   |            {unit consumption} + {no residual} cannot be assembled
   |            from the natural cell family.  What the house probe
   |            measured (C3 spec, 202/202 exact) is the reason: Gram
   |            violations displace flip AND census TOGETHER, so the
   |            house identity survives where index-1 fails.  The
   |            correct target is therefore NOT per-cell index 1 but
   |            the compiled flip-count inequality — which is what
   |            two_cell_pairs_flip now feeds, needing only |B| < A/2.
   |            ★ HIGH FLIPS 2026-08-28 ★ SeatingHighFlips.lean (std axioms):
   |            rh_of_high_flip_visibility — the Hardy-detector hypothesis
   |            (census-many XiLine sign flips per box) needed only in boxes
   |            above 1269/2.  ALL THREE register forms now localized to the
   |            same band: census (seating), flips (Hardy), boundary limits
   |            (HP receiver — further pinched to the log⁻⁹ shell).
   |            SPEC REGISTERED 2026-08-28: C3_SEATING_SPEC.md — event = harmonic
   |            completion (despun-readout flip, bank sums only); boxes = clock
   |            cells θ = kπ; target = F(box) = stripZeroCountMult(box).
   |            PROBE (pre-registered rules, tmp/c3_seating_probe.py): 202/202
   |            cells EXACT on (0, 400], zero PAIR/DEFECT — exceeded the
   |            registered prediction (PAIR at g₁₂₆ never fired: Gram-law
   |            violations displace flip and census TOGETHER, so the identity
   |            is insensitive to Gram/Rosser phenomenology; its only failure
   |            modes are off-line, multiple, or flip-invisible events — the
   |            certificate's content is purely RH content, no classical noise).
   |            HP capstone (08-11): "resolvent trace + EXACTNESS iff; ONE box
   |            = the seating."  STRONGER-and-constructive (candidate risk, not
   |            estimate risk: seating of THIS H is not RH-equivalent).
   |            In-tree: ZeroCountJensen, DVP count lanes, exactness iff.
   |            ★ T★ FLIP–CENSUS CONSERVATION COMPILED 2026-08-30 ★
   |            (adjudicator directive: the weakest exact theorem converting
   |            a ΔS-excess into equal flip-excess; Sam's precision honored:
   |            attained finite MAXIMUM, no supremum)
   |            SeatingFlipConservation.lean (std axioms, build 9621):
   |            even_mult_no_flip — even ζ-order repels the flip (same-sign
   |            edges) + isolation window, from the local ξ-factorization
   |            (order finite by riemannXi_analyticOrderAt_ne_top);
   |            flip_yields_odd_zero — a sign change forces an ODD-order
   |            on-line zero strictly inside (strong induction on the
   |            finite window census; even zeros push the flip aside);
   |            flips_le_oddOnLine_ncard — UPPER: every admissible chain
   |            has ≤ oddOnLineBox(open box) many flips;
   |            exists_uniform_delta_odd — mult-1 → Odd hypothesis swap in
   |            the uniform-δ kit + a RIGHT margin (g + δ ≤ T₂) so the
   |            packed chain is box-admissible;
   |            exists_odd_census_flip_chain — LOWER at the exact census:
   |            packing floor (gs.length+1 ≤ points) and the upper ceiling
   |            PIN the packed chain's length to census+1 — the maximum is
   |            EXHIBITED.  THE FACTORIZATION (T★):
   |            high_flip_visibility_iff_flip_census — the compiled door
   |            hypothesis ⟺ stripBox.ncard ≤ oddOnLineBox.ncard per high
   |            box.  H2 SPLITS: the co-displacement/analytic half is now
   |            UNCONDITIONAL (the conservation law HOLDS in C₁ — it
   |            survives the exact configuration that falsifies every
   |            door); the residual is ONE integer equation per box,
   |            D := strip − oddOnLine = 0 (D ≥ 0 compiled:
   |            oddOnLine_ncard_le_strip), and D counts exactly the
   |            R-normal-form poles — the leaf verbatim (no off-line, no
   |            even-order on-line), disguise stripped by a theorem.
   |            Doors: rh_of_high_flip_census (≤ form),
   |            rh_of_flip_census_conservation (equality/registration
   |            form).  Classical shadow named at source: Turing-method
   |            bookkeeping (sign changes + RvM), here as exact identity.
   |            BUILD NOTE RESOLVED for this composition: Zeta23.Statement
   |            (zeroMult) is Rectangle-FREE, so the clash was import
   |            hygiene, not substance — SeatingChain reduced to Detector,
   |            SeatingOddFlips to Detector+DVPWeightedCount+Zeta23.
   |            Statement, SeatingHalfFlips takes Transversal directly;
   |            the odd-flip kit co-imports with the PNT+ ladder door.
   |    Tombstone honored: same-λ C-equiv UNSATISFIABLE (hp-pencil-seat, 08-14) —
   |    the pencil equivalence route is dead; the seating route is not it.
```

## Guard (rule 11), current verdict

N1, N1′, N2, N3, N4, N5 are all `EQUIV` — the terminal open node is equivalent to the
target, so **this is not yet a proof plan**. The non-EQUIV live content:

* Road A: N3a/N3b compiled unconditional regions; N3c open (the shallow channel is RH's
  content in seat coordinates).
* Road B: N4 is the **compiled `STRONGER`-and-constructive identity** the guard demands
  (exhibited, discharged by Fubini, not estimate); N5b/N5d/N5e are constructive non-EQUIV
  leaves (kernel lemmas and regions, not restatements).
* The two roads converge on the same residual: zeros approaching the line. Rungs move the
  frontier; the close needs a structural collapse (precedent: ledger 340's fixed-center,
  the Erdős cell collapse). Collapses have appeared while laying rungs, not while planning.

## The two certificate registers for N5 (Sam's knob architecture, 2026-08-27)

The closed-form control law (the bank-derived π/3 correction, `corrFull = −ΞKernel/8`,
COMPILED O23/O24) admits two certificate forms; both discharge N5's content:

* **Sign register (current mainline):** `Khat ≥ 0` on the strip — every potential
  off-line completion excluded pointwise.  The rung ladder climbs this.
* **Count register (OPEN, candidate reorganization):** the law's on-line completions
  tally to `N(T)` per box — an integer equality.  Manual per-event knob control is
  `∀ event ∃ setting` (not a theorem: no uniformity — the classical mollifier ceilings
  are exactly this gap); the closed form buys `∃ law ∀ event`.  Native here because the
  harmonic register's count decomposition is exact (2026-08-12 law: the count IS the
  event count; no S(t) to fight — the classical obstruction to counting proofs is
  dissolved by register choice, not estimated).  Counting machinery in-tree:
  `ZeroCountJensen`, the DVP count lanes.  Outside the zeta-23 Prop-7.4 instrument
  class (exact registration, all events, no finite-moment compression).

## Measured constraints on any N5 proof (each kills an attempt class)

1. **s-averaged only** — N5c refuted pointwise (the cancellation is between s-cells).
2. **theta-specific** — `model_slice_neg` compiled: the kernel-free model goes negative.
3. **no total-positivity shortcut** — `dKernel_rank_one` compiled: the kernel is rank one.
4. **sharp cell constant is π** — measured, forced by the s→0 limit.

## Session ledger (2026-08-28, X₀ = 3 compiled)

2026-08-27: N1″ (live-repo wiring, 8 thms); rung-1 X₀ = 1/2 (O61–O66, 38 thms);
Turán sign whole half-line (O67–O68); kernel antitonicity (O69); THE SHARP π-CELL
(O70); cell toolkit (O71); |cos|-cancelled criterion (O72); 12-piece staircase
(O73); near enclosure (O74); scaled nodes + tile floor (O75); t₀ engine
(O76–O78); c-band plan certified 2.84× (o79 v1→v4 — two of my own claims
refuted by controls: the (x,s)-grid design and the "far tail tiny" note);
band mirrors (O80–O81); anchors (O82); 451 generated t₀ points (O83–O101);
17 stairs + 17 tiles (O102).
2026-08-28: pointwise layer (O103); integral glue (O104); evenness (O105);
strip numerics (O106, 35 thms); THE ASSEMBLY (O107, 31 thms) →
**numerator_im_nonpos_band_three COMPILED, std axioms** — budget asserted in
exact rationals at emission (head 4.45e-4·y vs deficits 2.85e-4·y).
Rung total O61–O107: ~820 theorems, all std axioms, escape-scans clean.
REFUTED/RECORDED: F-transform certificates (o60_ftail); head-vs-deficit shape
(prework v1); pointwise-in-s (N5c); e^{s/2}-envelope (budget assert, −3.6e-5 →
cosh two-sided fix).
QUEUE: X₀ ≈ 8 rung — scaling law FIRST (head window dies ~X₀ ≈ 3.5 in current
design; per-column head is the candidate; prework before proof); O-lane port
into RequestProject (task 5) so N1″ ∘ rungs chain in one tree; Road C seating
probe spec; pitch-aligned probe; LEDGER_O_E59 → adjudicator.
