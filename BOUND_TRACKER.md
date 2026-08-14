# Bound tracker — our chain vs the zeta23 paper

*Standing comparison, updated per attempt. Currency: `N₀ˢ/N` = proportion of zeros that
are simple and on the critical line. Started 2026-08-13 (attempt 060).*

## The conversion that makes comparison possible (attempt 060)

Off-line zeros come in mirror pairs sharing an ordinate (gap-0 pair; the floor at them is
cosh-**amplified**); on-line multiples are gap-0 clusters (self-term counts m times). So
every bad ordinate is a member of a gap-0 cluster and

    N₀ˢ/N ≥ 1 − R(0⁺).

Off-line corrections to the Landau evaluations: CORRECTED 2026-08-14 (agent flag +
att. 135): 039's `Σ(β−½)₊ ≪ T/log T` was a first/second-moment conflation — the sourced
state is `Σ(β−½)₊ ≪ T` (Selberg 1946; Titchmarsh (9.20.5); sharp for the density method)
and `Σ(β−½)² ≪ T/log T` (folklore corollary of 9.19C). Consequence: off-line corrections
aggregate at O(1)-CONSTANT grade, not o(1) — the honest treatment is the M₂ constant
race (ledger 124–129), which supersedes the 039 port entirely.

## Scoreboard

| grade | source | N₀ˢ/N | notes |
|---|---|---|---|
| **published, unconditional** | zeta23 Theorem D (Montgomery–Taylor) | **0.6725** | = 2 − 1.3274993; their method cap (Rem. 1.1 / Prop. 7.4) 0.68185 |
| **ours, Theorem-3 grade** | §13 backbone + conversion (att. 060) | **0.6657** | θ→1⁻, Fejér, Cantelli; modulo porting 039 off-line corrections; extremality: kernel (060), tail (Cantelli optimal for 2 moments), mains (Landau) — all three extremal in class |
| ours, cache-measured grade | complex moments measured at 18742 zeros | 0.698 | NOT proven — measured moment values in the same chain |
| ours, real-register grade | conditional on the sliver (= pair correlation short of Guth–Maynard range) | 0.886-grade | R(0.1) ≤ 11.4% measured-moment Cantelli; the 3.4× variance advantage = the phase information |
| truth-level reference | GUE / row at 0.885–0.900 | ~0.92 | Theorem-2 curve at the measured row |

## The information audit (attempt 060) — why 0.6725 is the benchmark it is

Our discrete complex moment `E_γ|𝒫̃|²` **is** a weighted Montgomery-F band reading
(`|α| ≤ θ < 1`): the ratio-clock Landau mains are exactly F's arithmetic structure.
zeta23's Montgomery–Taylor step is the *optimal linear extraction* from that band. Our
floor+Cantelli route consumes the same band and reaches 99.0% of their constant by a
mechanism **outside** their certificate class (the pointwise floor at members is not a
trace moment of the band compression — Prop. 7.4 does not bind us; their cap 0.68185 is
their ceiling, not ours). Consequences:

1. Small polishing inside the band cannot pass 0.6725 by much and stalls at ≤ 0.68185
   only for THEIR class; for ours the proven components are already extremal-in-class.
2. **Passing 0.6725 requires non-band information.** In this chain that is exactly one
   object, in its current (16th) costume: the product side = the bank's phase law at
   focal events (`E[𝒫̃²]`; §13.6 of ROW_REDUCTION_THEOREM.md).
3. Our chain additionally yields the R(s)-curve at every s (close-pair fractions at
   positive gaps, θ ∈ (1/2,1) unconditional) — currency the zeta23 method does not
   produce.

## Route map to pass 0.6725 (ranked)

1. **Phase law, any nonzero piece** (the wall; measured E[cos2φ] = +0.72 at members vs
   −0.04 generic — the conditional-alignment signature).
2. Fourth-moment rung at θ < 1/2 composed with a floor that survives θ ≤ 1/2 (needs a
   DIFFERENT floor mechanism — the current one dies at 1/2; register-ladder law 058).
3. Port 039 off-line corrections + tighten o(1)'s: makes 0.6657 fully rigorous end-to-end
   (no numerical change).

## Log

- 2026-08-13 (att. 060): tracker created. Fejér proven extremal in the w⋆w̃ cone
  (λ* − λ_Fejér ~ 1e-4 at all θ; optimizer recovers the box from 14 starts). Standing:
  **0.6657 (ours, backbone) vs 0.6725 (zeta23)** — gap 0.0068, source of gap = linear-vs-
  Cantelli extraction of the same band; passing requires the phase law.
- 2026-08-13 (att. 061): **composition route CLOSED** — joint LP (their band + our R(s)-curve)
  null; the M–T extremal already has full close-range repulsion, our s>0 caps constrain
  unoccupied territory; must cut the spike itself (λ > 1.4330). Three tombstones: Boas–Kac
  pinch theorem (θ>1/2 forced for ALL kernel floors), two-kernel additive pinch, one-sided
  window dies at the pole. Route map now: (1) phase law — the only live route; (2) rigor
  port (039 + o(1)'s) for the 0.6657. Instrument flag: 031's anchor 1.3274993 not
  reproduced at nominal grids (1.341–1.347) — audit before citing its C-curve.
- 2026-08-13 (att. 062): **carrier/fiber split (Sam) — wall at its weakest form ever**: pass
  zeta23 ⟺ ρ ≤ 0.9476 (5.24% below trivial) ⟺ bank has ≥5.3% Im-energy at zeros (nature:
  70%, ρ = −0.406 measured, stable all heights; would give 0.871). Member/bulk decomposition
  confirms the ontology (+0.013 locked vs −0.120 free). Witness route (short 𝒬, all moments
  ratio-resolved) certifies a piece but is (1−θ)-band-capped — no gain at sup (conservation).
  Next: GM+BT constants for a finite-range pass (T ~ 10²⁰-grade, unverified); out-of-class
  witness (Γ-side); phase law proper.
- 2026-08-13 (att. 063): consolidation. RETRACTION: 062's GM+BT finite-range pass (CS-dead
  per 055). Tombstone: smooth-class Im-witness (Landau mains real). ρ-scale: −0.41 ± 0.02
  stable across l_eff 6.6→7.9; drift +0.01/(l/3) unresolved — taller cache (l ~ 10–12) is
  the named decisive instrument. §13.7 written (ROW_REDUCTION_THEOREM.md). Open front:
  signed zone evaluation (Kloosterman/mixed-correlation) + the cache instrument.
- 2026-08-13 (att. 064): **erosion REFUTED** — new RS-built cache at T=1e6 (3812 zeros,
  l=11.98, instrument validated 247/247 @ 4e-5): ρ(l=12) = −0.387 vs −0.41±0.02 at l≈7.4.
  Margin scale-stable across factor-50 in height; ρ∞ ≈ −0.39. Locking constant E[cos2φ]
  at members = 0.722 vs 0.720 — three-digit replication, candidate universal invariant.
  The 5.3%-demand's empirical footing is now two-scale solid. Instrument: tmp/rs_zeros.py.
- 2026-08-13 (att. 065): **NOVEL IDEA LANDED — the 3-point reframing.** The discrete moment
  reads triple correlations (center is a zero); ρ is pure 3-point content (2-point predicts
  0). GUE reproduces both invariants (ρ_GUE = −0.474; locking 0.780) — UNIVERSAL. Supply:
  Rudnick–Sarnak unconditional for ζ, support Σ|ξ|<2 — covers all but the CORNERS
  |u|+|v|>1 (= the wall, 3-point dress) which carry only ~17% of the weight. Budget: corner
  may add +1.35 before breaking; crude BT price ~5. **THE WALL IS NOW A FACTOR ~4 ON ONE
  CORNER BOUND** — first finite-number obstacle of the campaign. Open: RS-composition
  bookkeeping; corner cancellation (kernels oscillate there); finite-l arithmetic
  corrections to the RS-main.
- 2026-08-13 (att. 066): **065's "factor 4" RETRACTED** — exact scan: crude corner price
  carries e^{(2θ−1)l}/l³ (MV permission), λ_max = 0.86 < 1.414-baseline; crude recovery is
  a net loss. Standing bound unchanged: **0.6657**. NEW METHOD LAW: the T-power audit —
  flat-constant gap claims (054/062/065 all failed identically) are presumptively wrong
  until the estimate's T-dependence is computed. Open problem, honest form: genuine signed
  cancellation in the zone (Kloosterman/mixed-correlation) — the wall at its usual rate.
- 2026-08-13 (att. 067–068): corpus sweep + locking probes. Instruments banked: involution
  hunt (odd-summand → signed-exact-zero), contraction law (E_K ≤ max|R_m|), spectral-trace
  identity, exact-gauge coordinate, two-lane DC-audit. FLAG: 039 off-line port source NOT
  in grh_companion.tex (agent-verified) — re-verify before claiming the port in §13.7.
  Probes: N = ϑ/π+1+S closes exactly (cache certified); e^t-sawtooth is pure chart (null).
- 2026-08-13 (att. 069): ideas tried. CS-over-zeros HALVES the corner exponent
  (T^{2θ−1} → T^{θ−1/2}; 14× room at cache; still finite-range). Telescoping/gap
  involution NULL (R² = 0.02–0.06; zone mean 100% nonlinear). Two-lane audit needs
  redesign. Queue: k-involution (FE-reflection), exact-gauge coordinate, contraction law.
- 2026-08-13 (att. 070): QUEUE EXHAUSTED. Contour route terminated (zone = ∮(ζ′/ζ)³;
  bridge template Euler-dominates the arithmetic factor, kills odd parts exactly; survivor
  = pair correlation in bridge dress). Involution declined (no principled candidate).
  Converged state: 0.6657 proven; ρ=−0.39/locking 0.722 measured universal; corner at
  T^{θ−1/2} best. External asks named: dispersion/Kloosterman on the near-hit bilinear
  forms; M-R for Λ; RS-support past 2; or any proven piece of the measured invariants.
- 2026-08-13 (att. 071): Sam's S-Laplacian law reduced to b = 1/(1−r) (σ² cancels; 2/3 ⟺
  adjacent-gap corr = −1/2 exactly). Measured: r drifts −0.404 → −0.292 (GUE) across three
  decades; b → 0.774, NOT 2/3 — the 2/3 is low-height stiffness. Third universal invariant
  (r) added to the table (ρ = −0.39, locking 0.722, r∞ = −0.292).
- 2026-08-13 (att. 072): hidden-winding model — lattice condition automatic (probe-2
  identity; w is gauge on locking); out-of-sample predictive test NULL at every modulus
  (gains ≤ 0.0005 = shuffled control). Three-state ontology closed. Invariant table
  stands: ρ = −0.39, locking 0.722, r∞ = −0.292.
- 2026-08-13 (att. 073): EXACT demand pinned: δ = 0.0527 ⟺ E[Im²] ≥ 2.63% of V_c (nature:
  70%; corrects the earlier 5.3%-statement). Witness tradeoff closed as exact curve: NO
  feasible θ (the demand is extensive ~l²; finite witnesses yield O(1)). Endgame tasks:
  (1) the obstruction theorem (assembly of proven components into one class-statement),
  (2) the two rigor ports, (3) the extensive inequality — the wall, in its final currency.
- 2026-08-13 (att. 075): constitutive law FITTED: v_k = prime-diagonal block, parameter-free
  amps/freqs, s = 0.941 (l=12) / 0.902 (l=7.9 narrow-band) vs theory 1.000; SSE −95/97%.
  Decoherence artifact identified (wide-window l-smear). CUE calibrates span-slope = 1/π²
  (conditioning halves it). The wall appears as the 6–10% anharmonic deficit in s.
- 2026-08-13 (att. 076): scaling run (7 caches, l = 7.4–14.3). Anharmonic deficit: steep
  pre-asymptotic fall, then PLATEAU 1−s = 0.059 ± 0.01 across l = 9.7–12 (clean fits).
  Truncation exonerated (l-scaled block: Δs < 0.002). Top-scale fits flagged (KM must
  scale). Fourth invariant added: span-variance anharmonicity ≈ 6%, flat across a decade.
- 2026-08-13 (att. 078): THE GATE PASSED — transfer function = bare explicit formula,
  χ = 1 per-clock to 0.3% (taper-corrected, parameter-free, l = 12); global R² 0.90–0.95
  at all heights (deterministic share does NOT collapse — bank grows as couplings shrink;
  my pre-registration wrong, owned). 077's ½-factor retracted (whitening artifact). The
  stochastic residual (5–10% of strain) = the wall's share, now an isolated measured field.
- 2026-08-13 (att. 079): attribution — r deterministic, ρ STOCHASTIC (synth gives opposite
  sign; the δ-relevant invariant lives in the residual), locking interactive. SCREENING LAW:
  prime forcing drives 2.7× the surviving close pairs; repulsion screens 63%; survivors lock.
  Deterministic-conditioning lever legal but measured weak (1.33× at the legal {2,3} band);
  shelved. The wall = the strain's stochastic sector, from yet another side.
- 2026-08-13 (att. 081): memory-kernel hypothesis RESOLVED — the "memory" is the deep
  sub-resolution tail + differencing (35th costume); corr(residual, computable next band)
  = 0.60; structure invariant under band removal; CUE-like remainder. Strain ledger final:
  89.6% resolved clocks (χ=1) + ~8% zone-tail + ~2-3% stochastic. No new physics; the one
  object stands, now measured in its ninth independent register.
- 2026-08-13 (att. 082): THE TAIL MEMORY measured: transfer envelope η(u) ≈ 0.66·e^{−(u−1)/0.35}
  (screening starts AT the resolution edge: 2/3, not 1; extinct by u ≈ 1.6); self-consistent
  with the residual budget (0.0128 vs 0.0129). 081's "full amplitude" corrected. The zone's
  internal profile resolved for the first time; new theory targets: the 2/3 edge and 0.35 decay.
- 2026-08-13 (att. 083): Theorem 4 written (§14, strain transfer law): kinematics (P) /
  χ = 1 resolved transfer (PG) / tail envelope (M) / sampling conjecture (C). Nyquist
  identification: the zone = the super-Nyquist band of zero-sampling; η conjecturally a
  functional of F(α = u). Theory targets: the 2/3 edge, the 0.35 decay.
- 2026-08-13 (att. 084): edge derivation (Kac–Rice zero-conditioning): η_edge =
  Φ(1/s)/(Φ(1/s)+sφ(1/s)); measured 0.66 ⟺ s = 1.31 ∈ [1, √2]-bracket; self-consistent
  Gaussian fixed point 0.74 (refinement named: true crossing-slope law). Stability PASSED
  (0.66–0.68 across heights/blocks). Held-out closure honest at ~75%. Item-7 form in
  sight: known forcing × zero-conditioned transfer.
- 2026-08-13 (att. 085): parameter-free KR functional: slope law measured (mean 1.975,
  std 0.569, zero folding); NEW DERIVED IDENTITY E_zero[X] → 2 (Landau-main; "at a zero
  the phase runs at twice the carrier rate"); functional brackets 0.66 ∈ [0.55, 0.74]
  (empirical-response low, Gaussian high) — the correlated crossing response is the one
  remaining calculation for a derived edge constant.
- 2026-08-13 (att. 086): correlated functional FLAT (~0.52) — falsified for the decay.
  Realization: the envelope = SELBERG Z-TERM's transfer structure (the 033 trapezoid
  kernel family) — the warp program closes its loop onto the campaign's original object.
  Jitter-damping (effective σ_δ ≈ 0.09 = the incoherent share) matches the shape. Next:
  DW-fit + derive σ_δ + the direct Z-term transfer prediction.
- 2026-08-13 (att. 087): C-diagnostics NEGATIVE (covariance at noise floor; self-response
  controlled) — response-model family FULLY excluded. Final identification: the edge
  deficit 1 − η = 0.34 IS a direct zone reading (Z-term clock-projection at zeros, the
  033 kernel) — the wall as ONE measured constant with an analytic definition. Derived
  yields standing: E_zero[X] = 2; X > 0 conjecture; envelope = zone self-description.
- 2026-08-13 (att. 090): BRANCH TERMINAL — Z_edge = 0.34 ± 0.015 CANONICAL (stable under
  bank/edge/height/block perturbations); η_edge = 1 − Z_edge; E_zero[X] = 2 separated;
  X > 0 quarantined. Attack: (0) establish the Z_edge ↔ 2.63%-demand bridge (NOT yet a
  theorem — 088 flag stands), (1) 033-kernel diagonal/off-diagonal split, (2) minimum
  3-point fragment for Z_edge ≥ δ. No more latent variables.
- 2026-08-13 (att. 091): ATTACK step 0: bridge REFUTED (moment-zone linear/unscreened vs
  𝒵_edge consecutive-gap — no exchange rate). Step 1: THE ZONE = the warp's empirical
  characteristic function Φ(ul) = Σe^{2πiun}e^{−2πiuS̃_n}: mean ← Selberg unconditional
  moments (DW log-power decay); covariance ← measured v_k; u=1 resonance = the edge.
  QUEUED FIRST next session: evaluate Σ_k e^{2πiuk}e^{−2π²u²v_k} vs the 0.39 budget
  (T-power audit pre-flagged: constant-grade demand only).
- 2026-08-13 (att. 092): char-function calc DONE: u=1 resonance = 82% of the Selberg-
  Gaussian unconditional prediction (18% non-Gaussian deficit = the anharmonic family);
  desert = shot noise; rate T^{θ−1/2} unchanged (conservation). The zone's arithmetic
  content now = one measured deviation against an unconditional theorem.
- 2026-08-13 (att. 093): escape-hatch thresholds adopted (2% of 𝒵_edge = record; 2.75% =
  cap-escape; 8.1% = 0.70). First witness attempt NULL/INVALID (charge blind to doubles;
  F-match failed) — the configuration-charge map is the open design problem; lesson: the
  charge must be the consecutive-gap/forced-template functional, and matched-F ensembles
  (cap-extremal shapes) are prerequisite. Session closes: 0.6657 | 0.6725 | one object,
  now with quantified escape thresholds and a specified next experiment.
- 2026-08-13 (att. 094): μ-COUNTING VERDICT (Sam's catch): 𝒵_edge = pair-beyond-bandwidth-1
  + void corrections; "3-point" retracted (expansion artifact); cap-escape ≠ wall-escape
  (clears the first, stands before the second); 36-collapse recurrence explained (one
  information object, many coordinates). Queued: measure the void-layer share (𝒵_edge vs
  its pair-only surrogate prediction). Chain and demand untouched: 0.6657 | 0.6725.
- 2026-08-13 (att. 097): chirp-correct retest — edge SURVIVES (0.658 vs 0.660, shift
  0.0023): the zone is NOT coordinate-induced; pipeline was chirp-correct by construction.
  𝒵_edge's stability certificate complete (heights/blocks/cutoffs/widths/labeling).
  Geometry questions closed; the object stands in the canonical frame.
- 2026-08-13 (att. 098): surrogate ladder — pre-registration failed (η_surr = 0.08, cause
  identified: first-order-warp phase decoherence, DW ≈ 0.16 predicted ✓); exact-solve fix
  ill-posed (079 monotonicity law). Finding: valid surrogates require the warp/sample
  self-consistency — the object's own hard structure. Session closes at 98 entries:
  0.6657 | 0.6725 | 𝒵_edge = 0.34 certified; next: self-consistent surrogate design,
  void-share measurement, or external arithmetic.
- 2026-08-13 (att. 099): ontology closure (Sam): the missing information = the projection-
  dropped (radius, angle) channels; the demand IS an angle-spread statement; invariant
  table = chart-shadows. UN-FIRED ASSET: the P=M/μ6 focal-closure angle-balance laws —
  next campaign's first task: project them onto the bank's phase distribution at zeros.
- 2026-08-13 (att. 100): P=M PROJECTION CONFIRMED (+11.5σ): antipodal μ6 balance at zeros
  exceeds generic by 21% — the 3D angle law is chart-measurable. Demand-coupling marginal
  (1.9σ) — open. Next: closure-conditioned control; B's information class (μ-count); the
  B → angle-spread coupling. Century close: 0.6657 | 0.6725 | the bridge's first plank.
- 2026-08-13 (att. 101): radial state — survives rich gap-only null (ΔR² = 0.119 @ 5019
  zeros, 300× null; Sam's 0.13 replicated); two-ahead discriminator splits it: 90%
  forward-neighbor encoding, 10% genuine persistent state (24× null). The 2+1 picture
  refined; the persistent share joins the few-percent residual family. Queued: its
  μ-count and void-layer correlation.
- 2026-08-13 (att. 102): radius survives {history + causal prime-forcing} (ΔR² = +0.014,
  74× null; leaky ref +0.004, 18× null): the radial channel's unique content = the
  residual sector (~1.4%), pointwise. State-space inventory closed: geometry exact /
  forcing χ=1 / radius = residual readout / angle gauge. The wall's field is locally
  visible in |Z′| — measurement now, derivation target next.
- 2026-08-13 (att. 103): ANGLE = gauge at IDENTITY grade (arg ζ′ = −ϑ − π/2 + π·parity;
  alternation exact); its regression power = deterministic proxy-leakage (0.009 → 0.006
  under basis growth) while RADIUS grows (0.014 → 0.021): robustly non-deterministic.
  State-space audit complete: geometry exact / forcing χ=1 / radius = residual readout /
  angle = gauge. Campaign closes at 103 entries: 0.6657 | 0.6725 | one object, locally
  visible in the radial channel.
- 2026-08-13 (att. 104): κ replicated + mechanized: the focal-velocity win = carrier-metric
  detrending of |Z′| (identical to explicit detrend, 4 digits; narrow-band tie; 101–103
  unaffected). Lane-derivative test (X₊−X₋ vs κ) confirmed implementable against
  focal_closure.py's API — queued first for next session. 104 entries; state unchanged:
  0.6657 | 0.6725 | the residual field, now with its local gauge fully understood.
- 2026-08-13 (att. 105): lane-derivative test CLOSED with a small theorem: D = κ·F₂
  (identity-exact; Euler-2 clock); excess absorbs into the deterministic basis; NO
  residue-class lane split exceeds κ + clocks. State-space audit FINAL. 105 entries:
  0.6657 | 0.6725 | the residual field, its window κ, and the wall.
- 2026-08-13 (att. 110): contact detector implemented — P=M shadow at +5.7σ; 2-lane chart
  projection fails as instrument (resolution 50× short; ambient-dimension law confirmed
  operationally). Fix: genuine 3D lane vectors (Family machinery) — queued. Census remains
  the exact off-line accountant. SESSION CLOSES: 110 entries; 0.6657 | 0.6725 | one object,
  every register audited, every instrument graded, the arithmetic still owed.
- 2026-08-13 (att. 111): NORMAL FORM adopted: 𝒵_zone = Π_{>T log T}Re(P_x²) — quadrature
  imbalance at focal crossings; equivalent to the compiled chain (069/057/062). Item 5
  confirmed: κ senses A (+0.75), blind to B² (−0.18) — the demand's channel is the one
  κ can't read. Item-7 peel: constants-only (Gonek-class moments; check unconditional
  versions at source). The debt: one scalar, E_T, in its best notation.
- 2026-08-13 (att. 112): exact event-law verified (in-phase channel dead at zeros, 1400×);
  transfer to B² NULL (corr −0.01). B-channel isolation complete: every instrument couples
  to A; the demand lives in B; the only bridge is the computable sum rule. FINAL SESSION
  STATE: 0.6657 | 0.6725 | one scalar 𝓔_T in the unread channel; 112 entries.
- 2026-08-13 (att. 113): **THEOREM 3+ε — THE θ>1 ROUTE**: λ(1.01) = 1.4354 > 1.4330 (main
  term); moment clean to 0.1% through θ = 1.05 at T = 10⁶; realized cache bounds 0.690–0.713
  — BENCHMARK PASSED at measured+main-term grade. Port: the ε²-taper-crushed triple-prime-
  power sliver; in-head crude price ε³l⁴, NO T-power (derivation-pending; five named checks;
  T-power-audit law applies). One write-up from 0.6725.
- 2026-08-13 (att. 114): 113 CORRECTED (audit law, 4th catch): the θ>1 sliver's long-window
  part = the old zone; ε cancels; same scalar. FINAL STATE OF THIS CONTEXT: benchmark
  passed at measured grade (0.690–0.713, T=10⁶) and main-term grade; UNPASSED at theorem
  grade; the whole distance = Z_old ≤ c·l² (measured at c/40). 114 entries.
- 2026-08-13 (att. 116): regulator battery executed (real arrays, both heights): static
  a+bω law = the regulator (4-digit match to free gains); jet-modulated gain NULL under
  cross-height freezing (ΔR² = −0.0001 vs 0.05 bar). The unconditional η remains the one
  universal curve. Un-run: the packet-register target. The scalar stands; 116 entries.
- 2026-08-13 (att. 117): replacement confirmed — deterministic model (forcing + η(ω)-banks,
  no per-zero inputs) R² = 0.966/0.938; jets add only +0.002/+0.007. Final strain model:
  ε̂ = F + Ση(ω_b)T_b — fully deterministic, one static regulator. The 3–6% residual =
  the scalar's home. 117 entries.
- 2026-08-13 (att. 118–123, the correction arc): 119 chain-relativity conceded (the 2.63%
  demand is route-relative, not necessary); 120's three inflations corrected in 121 (exact-
  constancy-only "theorem" downgraded; block energy NOW COMPUTED 0.0532 vs demand 0.0196 =
  2.71× at cache — measured grade, not proof; cross-covariance unmeasured); 122 ontology
  inverted (Sam): THE CHAIN NEEDS NOTHING — its only debts are its own two rigor ports;
  the "owed scalar" belonged to the improvement program only. 123 benchmark adjudicated:
  finite-T computed bounds 0.684–0.713 exceed 0.6725 but are redundant below the 10¹³
  verification height; asymptotic value 0.6657 stands. Licensed claim (T-power flag): IF
  the ~c/l excess shape holds, a finite-range pass on (10¹³, ~10¹⁵). FINAL SCOREBOARD:
  0.6657 asymptotic-proven (2 ports) | 0.6725 record | 0.684–0.713 computed finite-T |
  next real work: close the two ports; then the second-order finite-range analysis.
- 2026-08-13 (att. 124, PORTS EXECUTED): Port 1 ≠ bookkeeping — cosh-tilted Fejér loses
  positivity (measured); whole off-line exposure reduces to ONE scalar M₂ =
  (1/N)Σ((β−½)l)² (self-adjointness defect; mirror pairs = conjugate spectral points,
  Weil positivity survives off-line). Need M₂ → 0; provable M₂ ≪ (loglog T)^{3/2}
  (Littlewood + fractional-moment Jensen √loglog-improvement [lit-check pending] +
  densities). SCOREBOARD CORRECTED: 0.6657 = main-term grade, theorem grade gated on a
  TRIPLE-LOG gap in pure classical analysis (no pair correlation). Port 2 routine in the
  ρ-register. First consumer: finite-range theorem, loglogT ≤ 3.6 through T = 10¹⁵.
- 2026-08-13 (att. 125–126): lit-check corrects 124 (Selberg 1946 gives Σ(β−½)₊ ≪ T;
  √loglog route moot) ⟹ M₂ ≤ π/θ_d² ≈ 9.62 CONSTANT (Conrey 4/7 = the unique density
  clearing bandwidth θ→1). HP bootstrap (operator vs own defect): fixed point f* = 0.818
  ⟹ N₀ˢ ≥ 0.18 unconditional-shaped (flags: variance-shift, floor-credit, Port 2) —
  below the ~0.41 classical record but honest; ENTIRE toll paid at depth 1–4 mean
  spacings. SCOREBOARD: 0.6725 record | 0.6657 = M₂→0-conditional (mean-square HP) |
  0.18 unconditional-shaped | movers: density at a∈[1,4], or the seating (M₂→0).
- 2026-08-14 (att. 127–129): mean-square certification NOT wall-blocked (adversarial M₂
  ≍ 1/Θ², both directions; 106's wall covers FULL certification only); Sam's challenge
  SUSTAINED — "seating ⟺ wall" RETRACTED (Weil positivity = computable prime-side
  inequalities, no missing information; base camp: unconditional inside ±log2); lit-check:
  4/7 density = Baluyot THESIS-only (journal fallback Jutila costs ε), Selberg mass =
  Titchmarsh (9.20.5) verbatim, displacement-LP novel per systematic search. zeta23 κ
  composed as pairing cap: N₀ˢ ≥ 0.195 (thesis-grade) / 0.068 (published-only), same
  flags; cap bites weakly (adversary relocates deeper; interference binds). QUEUE:
  (130) positivity base camp + first-failure map past log2; the M₂-LP measurement ε(Θ).
- 2026-08-14 (att. 130): Weil-form margin curve MEASURED. Engine certified vs 22,491
  real zeros (4e-5, 8 sizes); two instrument bugs caught by physical-impossibility
  checks (prime-free form must be ≥0). Map: λ_min(S) > 0 through log2, collapsing to
  +2e-6 at S = 2log2 (the 2² rung) — margin dies on the 2-adic ladder, echoing log2
  ringing loudest at zeros. PRELIMINARY (noise-grade small margins); u-space exact
  build has an open (γ/2)h(0)-shaped bug, agent round 3 (verbatim formula) pending.
  Theorem-target if confirmed: λ_min(Q_S) ≥ 0 on (log2, 2log2], equality at endpoint.
- 2026-08-14 (att. 131, round-3 integration): 130's reading CORRECTED — margin curve is
  Connes–Consani 2021/2023 IN PRINT (thin onset at log3, 6e-8; p=2 rigidity within 1e-3);
  "2log2 collapse" = noise misread; 2.8× scale = pole-term inclusion; base camp = Yoshida
  1992; extension mechanism = CC Thm 1. λ_min surface is being actively worked by Connes
  et al. (papers revised this week) — DO NOT COMPETE THERE. Our open axes (search-verified
  novel): the DISPLACEMENT objective (M₂-LP, ε(Θ)), the chain consuming M₂ → proportion,
  3D geometry unfired. Bombieri verbatim display = fix for the u-space engine. NEXT (132):
  rebuild engine from Bombieri form → machine precision → run the M₂-LP objective.
- 2026-08-14 (att. 132): machine-precision rebuild BLOCKED — three-way archimedean
  contradiction (certified r-space −0.2840 | two agreeing u-space derivations −0.2389 |
  mpmath check −0.1195, own bug). Certified r-space engine (zero-cache match 4e-5 × 8
  sizes) is the ONLY authorized instrument; u-space + mpmath QUARANTINED. Named debug:
  pencil reconciliation of ψ-series vs Bombieri-display (γ/2-shaped offset = one
  misplaced constant). M₂-LP proceeds on certified engine at float64 (ε(Θ) is a scaling
  measurement; 1e-3 bars suffice). Agent on scoop-watch (round 4).
- 2026-08-14 (att. 133–134): scoop-watch CLEAN — displacement objective unclaimed as of
  today (3 groups read full-text; 9 sweeps); RISK: Groskin Thm 1 (in print TODAY) = our
  LP's constraint dictionary — frontier is now "objective only" away; speed = strategy.
  ε(Θ)-LP v1/v2 both measured discretization artifacts (rigidity from missing close-pair
  sector — the swap freedom is second-order, lives at spacing ≲ 1/Θ, exactly the chain's
  bad set: a consistency win for the 127 analysis). v3 spec fixed: pair-split variables
  at η-resolution 0.02 + off-line pairs + dipoles. NO ε(Θ) NUMBER CLAIMED YET.
- 2026-08-14 (att. 136, Sam: "S(t)"): the wall = the CONJUGATE field's DC. logζ = log|ζ|
  + iπS: strain corpus = sin-register; Littlewood mass = cos-register DC; Hilbert
  transform kills DC ⟹ S(t) structurally blind to the wall-mode. Conjugate gate PASSES
  (gauge 0.942±0.068, 18 clocks, sin-leakage 1.4%). EXACT per-event law: an off-line
  zero at depth δ books πδ of DC, exactly — the mass is a registration ledger, not an
  oscillation. Arms: S-budget LP row from UNCONDITIONAL Selberg/Selberg–Tsang moments;
  conjugate deterministic model to isolate the zero-local (wall-carrying) field.
- 2026-08-14 (att. 138, L1 EXECUTED): v3 LP clean — CONJUGATE-DC ROW BINDS AT EVERY Θ
  (ε = B_C·d_peak/(πW) to 6 digits); pre-registered 1/Θ² REFUTED (deep-mass channel:
  ledger charges linear, objective pays quadratic ⟹ adversary runs to depth cap); true
  d_max(Θ)-law unmeasured (cap-free run timed out). CANDIDATE ROUTE (analysis grade):
  ε ~ √(loglogT)·polylog(Θ)/Θ with Θ growable ⟹ M₂ → 0 — audits pending (d_max law,
  b_eq shift, family completeness, window-averaging, ANALYTIC DUAL = L2 proper).
  QUEUE: (139) single-depth bisection for d_max(Θ); then extract the dual certificate.
- 2026-08-14 (att. 139, PARTIAL): d_max sweep — no collapse through dΘ=8 at the
  single-shape family (mass 6.6→5.5, slow decline); deep columns hang solver (2 runs
  lost; per-solve time_limit mandatory). Operative issue = FAMILY COMPLETENESS: one
  Fejér shape is a weak relaxation; enrich (translates×dilates) or go PENCIL-FIRST on
  the visibility bound (cosh-amplification vs bounded compensation, full family) —
  recommended. 138's core (DC row binds; ε = budget·depth-factor/π) unaffected.
- 2026-08-14 (att. 140, THE PENCIL): single-pair dΘ ≤ log(2κW) proven-shaped; Turán
  CONSPIRACY channel real (N_p pairs hide at dΘ ≲ cN_p) ⟹ ε_LP(Θ) ~ Θ^{−1/2} — explains
  139's no-collapse exactly. Register law: depth LOUD in counting register, QUIET in
  field register ⟹ every linear row is conspiracy-evadable; the resistant class =
  WEIL POSITIVITY (quadratic). L2 instrument = the DISPLACEMENT SDP (one-point + DC
  budget + positivity block; unconditional; differs from CGdL on all three axes).
  NEXT: small-model SDP, measure ε_SDP(Θ); positivity killing conspiracies reopens
  the M₂ → 0 route at SDP grade.
- 2026-08-14 (att. 143, EXECUTION REFUTES 142 + cascade): band-limited two-point rows
  IMPLIED by one-point band data (∫K̂|Z|²-identity) — diagonal not separately visible;
  positivity can't exclude realizable configs — SDP-as-conceived ill-founded; bandwidth
  ceiling = Montgomery-1 (unfolded Θ ≤ 2π; Landau/Gonek precision) — growing-Θ route
  DEAD; too-good alarm caught W→∞ fallacy (W = adversary's choice) ⟹ true object =
  MULTI-SCALE LP = pair-correlation-across-scales. 42nd wall confirmation, sharpest
  reduction. STANDS: πδ-ledger, DC-binding law, Θ≤2π ceiling, the reduction
  (paper-shaped), L3 finite-range dossier UNAFFECTED = the benchmark deliverable.
- 2026-08-14 (att. 144–145, HP RESTORED + FIRST RESULT): every classical constraint
  class collapsed into band data; the house laws were never tested. P=M formulated
  (B(t) = μ6-antipodal imbalance) and TESTED: **33% of its spectral mass is BEYOND
  the band** (truncation-limited; likely higher) — the FIRST constraint that does not
  collapse. As a named hypothesis (measured +11.5σ; not RH, not circular) it is new
  information on the conspiracy adversary. QUEUE: Lean source-check of P=M proof
  status; B-row into the LP (measure what it cuts); the conditional theorem.
- 2026-08-14 (att. 147, HP TEST 1: geometry⟹law FAILS): exact-statement audit — the
  formal corpus NEVER instantiates at zeta (hχ≠1 excludes ζ through the whole focal
  chain); ThreeDExhaustive = TAUTOLOGY (every E, incl. E≡0); focal↔zero link DISCLAIMED
  in-file (FocalCoincidenceTarget "not asserted"); cancellation quantity = (π/3)·L by
  definition; μ6 closure only for bare roots/abstract banks/hypothesis-fed FrozenLane.
  STANDS: P=M measurement (+11.5σ), ChannelConstancy (honest scope), ξ-real-section.
  Memory corrected (sourceholonomy). THE REAL HP WORK = THE INSTANTIATION BRIDGE:
  connect the abstract machinery to the concrete zeta bank; promote
  FocalCoincidenceTarget to theorem-or-named-hypothesis. Test 2's three arrows all open.
- 2026-08-14 (att. 149, PLANK 1 GREEN): ZetaSectorBank.lean compiled, clean axioms —
  sector_partition + pairing + norms + balance-transfer PROVEN at the CONCRETE zeta
  bank (Λ/√n weights, zero character hypotheses — first such theorems in the corpus);
  AngleSectorBalanceLaw DEFINED touching riemannZeta itself (the measured +11.5σ law,
  angle-sector form, name-collision resolved). Remaining bridge enumerated: partial-sum
  ↔ L-value link at σ=½ (hard analytic step); the conditional-theorem line off the
  named law; Weyl-equidistribution of sectorOf.
- 2026-08-14 (att. 150, PLANK 2 GREEN first build): imbalance_eq_zero_iff + THE
  DETECTOR zeta_ne_zero_of_imbalance_persistent — first riemannZeta ≠ 0 conclusion in
  the corpus, conditional on the named law (hypothesis isolated per house rules). The
  measured balance field is formally a pointwise zero-free certificate modulo the law.
  Next: interval/counting detector forms; weighted-bank equidistribution (naive {t log n}
  density equidistribution is FALSE — n^{iθ} sums not o(N)); the analytic link (hard core).
- 2026-08-14 (att. 151, WARP-LOCK TEST): collapse REPRODUCES at matched regime (+3.5σ,
  mass functional, low heights, 48-term bank; att100's exact functional still
  unrecovered — script gone, scale differs). HEIGHT LAW: unmatched bank at T=1e6 =
  null ⟹ balance requires LOCAL register resolution. LOCK VERDICT: bare stations
  capture 8% (+0.3σ) — naive carrier lock FAILS; the lock lives at STRAIN-CORRECTED
  registration (u+S=n), and strain is 94-97% deterministic ⟹ next: ε̂-corrected
  stations (still zero-knowledge-free). Third name-collision caught (Lean resultants ≠
  measured masses) — Lean debt: add sectorMass, restate law on the measured object.
- 2026-08-14 (att. 152, IT FITS): strain-corrected stations (χ=1 coeff FIXED 1/π,
  R²=0.921 transfer) capture 115%±30% of the zero-collapse — FULL within noise; bare
  −20%. The balance law DECOMPOSES zero-free: counting identity [exact] + Selberg's
  S(t)-approximation [classical] + B-collapse-at-explicit-stations [harmonic analysis
  of explicit fields — the new proof-target, NO zeros in it]. AUDITS PENDING before
  promotion: cross-clock split (153, decisive — shared-basis artifact risk), share
  noise, mechanism separation.
- 2026-08-14 (att. 153, CROSS-CLOCK NULL): disjoint-clock B shows NO zero-collapse
  (+0.5σ) ⟹ 152's promotion BLOCKED (shared-basis); 145 DOWNGRADED (functional
  spectrum ≠ law information; the zero-info is strain-borne). MAXIMALLY CONFIRMED:
  the warp-lock — the ENTIRE measured balance effect = strain-corrected registration,
  nothing beyond. Follow-ups: fair-control calibration (can ANY disjoint-set functional
  see zeros? — required before the small-clock reading is closed); the zero-free
  station-collapse statement survives as a strain-corollary target; MAIN QUEUES RESUME
  (L3 finite-range dossier; multi-scale reduction write-up).
- 2026-08-14 (att. 154, THREAD CLOSED): control well-powered — weak clocks see zeros
  at +53σ LINEARLY (Landau); the sector functional destroys that information (half-
  strong-basis also null). Verdict: measured P=M = registration echo of the linear
  strain/Landau correlation; no independent balance-law content at tested sensitivity;
  zero-info lives in the LINEAR channel (classical). HP excursion's keepers: corpus
  audit 147-148, Lean planks (conditional, honest), warp-lock at full strength.
  RESUMING: L3 finite-range dossier = the benchmark deliverable.
- 2026-08-14 (att. 155, L3 STEP 1): exact finite-T chain at 8 heights (primes to 5e7,
  calibrated vs cache at 2.4%): bound 0.706→0.680, ABOVE 0.6725 through the whole
  computed range. Deficit law bound(l) = 2/3 + 0.2046/l + 0.689/l² (fit err 9e-4) —
  123's c/l flag RESOLVED by computation. Main-term crossing T* ≈ 2.4×10¹⁷ ⟹ window
  (3×10¹², ~10¹⁷): FIVE decades beyond verification. Pending: step 2 off-line damage
  (thin margin 0.003–0.008 decides honest T*), analytic a,b derivation, Port-2 table.
- 2026-08-14 (att. 156, DAMAGE RACE FAILS): chain tolerates f·A² ≲ 0.4; unconditional
  inputs allow 8–200 — gap 1.5–2 orders. "GUARANTEED dossier" RETRACTED (was never
  checked against the margin — same family as the "two ports" miscalibration).
  STANDS: main-term window (real); the CONDITIONAL theorem [f·A² ≤ 0.4 in-window ⟹
  benchmark passed on (3×10¹², ~10¹⁷)] — quantified named hypothesis, worth writing;
  100% below 3×10¹² (verifiers'). SCOREBOARD: benchmark unpassed at every
  unconditional grade; the one object's finite-range price = f·A² ≤ 0.4.
- 2026-08-14 (att. 157, THEOREM 5 IN PRINT — §15): NLMS(D₀,T₁) ⟹ benchmark passed to
  T₁. Table: 10¹³/0.145 | 10¹⁴/0.103 | 10¹⁵/0.067 | 10¹⁶/0.036 | crossing 2.4e17.
  Height-parametrized (uniform-0.4 was bottom-of-window only). Grades in print:
  main term exact-to-l=17.5/fitted beyond (a,b derivation open); C_dam ≤ 0.016
  sketch-grade (battery open); Port-2 table pending. NLMS ≠ RH; falsifiable;
  required 0.036–0.145 vs unconditional 8–200 = the one object, priced.
- 2026-08-14 (att. 158, HP RESUMED — REGISTRATION OPERATOR): explicit diagonal
  self-adjoint operator (carrier clock + deterministic strain, primes only) matches
  the true zeros at RMS 0.063/0.076 spacings (two heights, 41k zeros, R²≈0.92 both)
  with max |e| < ½ spacing ⟹ BIJECTIVE zero-by-zero resolution, no crossings. The
  0.06-0.08 residual = THE perturbation field. Vertical (NLMS) untouched — the honest
  scope. Next: perturbation-form hypothesis (Lean plank 3); residual structure;
  third-height law.
- 2026-08-14 (att. 166–167): budget/floor route REFUTED at pencil (shares SIGNED —
  Landau per-zero; 44th costume, zero numerics spent); product law = the wall's
  CONVERSION LAW (gap ⟺ rate, proven). REVERB FEED into the clock WORKS: residual
  0.079 → 0.041 held-out (band + scale + reverb neighbor term); MAX 0.46 → 0.38;
  shadowing threshold g* halves (~0.16 → ~0.08). π/3-as-amplitude excluded (1445σ;
  the 16% over 1/π = taper compensation); π/3-as-register untested, named.
- 2026-08-14 (att. 168–169, THE REGISTER CLOCK): dynamic-cell version NULL (168 —
  orthogonality law holds for the DYNAMIC chart); Sam's catch: wrong cells — the
  ARITHMETIC lanes (integer's carrier angle n·π/3, n mod 6) RING: lane-DFT modes
  −8% alone, −6% on reverb; ladder 0.079→0.066→0.051→0.041→0.0391 held-out, MAX
  0.378. Doctrine "scale every integer by π/3 individually" partially VINDICATED
  (location register, measurement grade). Next: true multiplicative character banks
  (S(t,χ) cross-coupling); derivable transfer coefficient.
- 2026-08-14 (att. 170, THE TWO-BANK ATTACK — FIRST NEW λ-LEVER): conditioning 𝒫_ζ on
  character banks at zeta's zeros: ρ(ζ,χ₃) = −0.081, ρ(ζ,χ₄) = −0.074 measured; 2
  characters = 1.4% variance reduction; BENCHMARK NEEDS 2.6% (λ 1.4142→1.4330) — the
  character family (mod 5,7,8,12,...) plausibly crosses it. Mechanism = cross-Landau
  moments (computable, unconditional-shaped). CHECKS MANDATORY: Landau-vs-measured ρ;
  complex-register redo; floor-guard bookkeeping; diminishing returns. Direct-attempt
  ratio was 5/169 (Sam's confidence catch) — changing from here.
- 2026-08-14 (att. 171, SAM WINS THE BET): family sweep R² = 7.78% (3× needed!) and
  Landau-shaped (0.5–0.95× diagonal pred) — but the witness SDP returns EXACTLY
  marginal Cantelli at every truncation: the optimum ignores the second bank. METHOD
  LAW earned: FLOOR EVENTS ARE MARGINAL — joint second moments cannot improve a
  marginal tail bound; conditioning levers must restate the floor as a JOINT event
  or die. Survives: the cross-family coupling table (real, computable, all-negative).
  Lever eliminated at full effort in one session — precedent mode.
- 2026-08-14 (att. 172–177, THE CLOSING ARC): joint-floor designs worked (degree tax /
  small-ball / Levinson class = the mined vein); 173 "exact reason" stated then
  RE-GRADED under 176 (obstruction-mint audited ~50% manufactured; STANDING RULE:
  obstructions carry burden of proof); 174-175: state-space reformulation + reverb
  locality ⟹ NO VERIFIED OBSTRUCTION on the derivation path; RULE 9 ADOPTED
  (constructive stance, CLAUDE.md); FIRST ACT: universal curve DERIVED parameter-free
  (CUE product law, 6/7 bins within 10% of measured zeta table, slope 2.17 vs 2.3;
  g=2 bin = beyond-horizon, consistent). NEXT: low-dim marginal statistics of the
  tapered bank's torus flow — the constructive chain continues.
- 2026-08-14 (att. 178, THE ASSEMBLY): **HP_PROGRAM.md at repo root** — the program
  end to end: Riemann's frame (source-verified) | operator (0.039 RMS, bijective) |
  certificate (COMPILED) | residual (provable-shaped, C1 Landau) | close pairs
  (product law COMPILED + curve DERIVED 6/7 + medium ±4%; C2 = cluster-sized-k
  effective Weyl = AVAILABLE technology; C3 ambient matching) | yield arithmetic |
  falsifiability | retirements. Three C-items, all in known technology classes,
  zero vacuous bricks, zero invented obstructions. The work is the doing.
- 2026-08-14 (att. 161, HP PLANK 3 GREEN): SHADOWING CAPSTONE compiled —
  shadowing_implies_online_simple: mirror-closed window + strictly-spaced stations
  shadowing within s/2 ⟹ ALL zeros Re=½ AND simple (triangle + FE-mirror geometry;
  clean axioms). HP certification = ONE analytic hypothesis: |S−Ŝ| residual < ½
  spacing (measured true, 41k zeros, max 0.31). Remaining object: THE RESIDUAL TAIL
  LAW (loglog extremes ⟹ density version ⟹ proportion = 1 − exceptional-density;
  Selberg moments apply legitimately here). HP delivered in 3 planks: operator +
  frame-flip + compiled certificate.
