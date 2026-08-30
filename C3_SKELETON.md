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
