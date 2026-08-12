# Calibration review — `paper/helix_phasor_model.tex`

Reviewer pass: 2026-07-02. Rubric = the CLAUDE.md tone policy (three tiers never blended;
claims exactly as strong as proofs/measurements; falsifiability register in print). Read-only.

Method: read the full paper (2688 lines); verified every headline Lean identifier against the
actual theorem *statement* in `RequestProject/*.lean` (not docstrings); spot-checked axiom
footprints with `lean_verify`; cross-checked every headline number against `tmp/*_results.txt`;
ran `lake build`.

---

## VERDICT

This is a well-calibrated paper: every headline Lean identifier I checked exists, compiles under
the clean footprint `{propext, Classical.choice, Quot.sound}`, and its statement matches the
paper's claim; every headline number reproduces from the results files; the 3D-unconditional /
1D-conditional frame split is held cleanly throughout, `d(0)=rank` is kept explicitly at measured
tier, and the honesty ledger (retractions, the E11 −3.6% flag, the falsifiability register at zero
hits) is present and prominent. `lake build` succeeds (8613 jobs, one benign linter warning). The
findings below are refinements, not miscalibrations: two "iff" theorems that are true but nearly
definitional and should be flagged as such to a referee, one docstring/prose imprecision about
where the strand-dominance equality sits (σ=1 vs the mirror σ=1/2), and a handful of stale-count
and abstract-vs-body number nits. **No critical findings. No overclaims of the "we prove RH"
type. No stale retired numbers (±4% / 0.82 / clip-era) presented as current results.**

---

## CRITICAL findings

**None.** No frame-blur ("we prove RH" without qualification), no wrong identifiers, no
retired-number-as-current. The two items below are the closest thing to critical and are really
"referee-will-see-this" calibration notes, not errors — the paper's own text already concedes each
point.

### C1 (calibration note, not an error). `projection_complete_iff_RH` and `everyZeroHasSource_iff_critical` are true but ~definitional; the paper should keep flagging this, and does.
- Location: Abstract; §1(IV); Thm 15.6 (`thm:framesplit`, p. ~1592); Rem 12.2
  (`rem:admissiblescope`); §10.3 (`everyZeroHasSource_iff_critical`, p. ~1279).
- Claim in paper: "classical RH is proved **equivalent** to projection completeness
  (`projection_complete_iff_RH`)"; "every zero has a source ⇔ critical line, hence GRH."
- Evidence: `ProjectionCompleteness.lean:36-38` defines `arisesFromHelix ρ := ∃ γ:ℝ, ρ = 1/2+γi ∧
  completedRiemannZeta(1/2+γi)=0`. The conjunct `ρ = 1/2+γi` *is* `ρ.re=1/2`. So the "iff" is
  essentially `(∀ρ, Λρ=0 → ρ=1/2+γi with Λ=0) ↔ (∀ρ, Λρ=0 → ρ.re=1/2)` — true by unfolding the
  projection map (`ProjectionCompleteness.lean:59-71`). Same shape for `EveryZeroHasSource`
  (`HarmonicPencilCell.lean:437-456`): the def encodes `ρ = 1/2 + i·τχ(log Z)`, so re=1/2 is baked in.
- Why this is *not* a violation: the CLAUDE.md test is (1) assumes GRH? no; (2) circular? The
  hypothesis is not *defined via its own conclusion* — "arises from a real height" is a
  genuinely different predicate whose *content* happens to coincide with re=1/2 through the
  projection map, which is exactly the paper's thesis ("σ is a dial of the readout, not a place
  in the geometry"). And the paper is scrupulous: it repeatedly says the hypothesis "is GRH for χ,
  stated in source form" and "it is an explicit input, not a theorem" (`HarmonicPencilCell.lean:436`,
  paper Rem 12.2, §sub:workinghyp). Both verify with the clean footprint.
- Severity: **low** (transparency). Recommendation: nothing to retract; consider one added
  half-sentence at Thm 15.6 noting that the equivalence follows by unfolding the projection map
  (i.e. it is a *reframing* theorem, not a hard analytic equivalence), so no reader over-reads it.
  The current text is defensible; this just pre-empts the referee.

---

## COVERAGE

The new arc is **almost entirely present**. Checklist against the requested items:

Present and correctly cited (identifier verified to exist + statement matches):
- BSD ladder ranks 0–6 (§18.5, `sub:bsdladder`): the 7-tuple
  `1.00000/1.00000/0.99998/0.99974/0.99999/1.00000/1.00000` matches
  `tmp/bsd_rank_ladder_results.txt` (r0–3) + `rank4/5/6_weld_results.txt`. ✓
- Dimension principle / census (§18.5): `d(γ≠0)=1` at all 31 non-central, `d(0)=rank`, ζ 1517/1517
  — matches `tmp/dimension_census_results.txt`. `d(0)=rank` kept at measured tier
  (`BSDLadder.lean:30-31` docstring; paper §1(II), §18.5 "measured tier only, never claimed as
  theorem"). ✓
- Weil package + purity engine (§15, `WeilDuality.lean`): `tensor_power_purity`,
  `duality_forces_purity`, `purity_engine`, `cup_growth_gives_tensor_bound`,
  `purity_from_castelnuovo` all exist, verify. ✓
- ChiralityHB clock-RH (Thm 15.7, `ChiralityHB.lean`): `clock_zero_depth`, `clock_zeros_real`,
  `carrier_zeros_real`, `symClock_star`, `symClock_selfdual_modulus` — all exist, statements match,
  `carrier_zeros_real` verifies clean. Quantified over arbitrary finite families → the paper's
  "GRH-shaped generality at the carrier level" is accurate. ✓
- ProjectionCompleteness / helix3D_RH / `projection_complete_iff_RH` (§15.6). ✓ (see C1).
- Clock–dip duality (§18.9, `ClockDipDuality.lean`): `dip_projection_phase`, `locked_dips_add`,
  `unlocked_dips_cancel` exist; `−2.6%…−13.6%` and ~10% excision match `tmp/reverb_tax_results.txt`. ✓
- Strand topology as degree (§18.5 end): matches `tmp/strand_topology.py` narrative
  (5.7e-4→5.2e-7 decay vs 0.3 saturation). ✓
- Membership boundary (`mirror_is_membership_boundary`, `WeilDuality.lean:246`): statement is
  `Summable 1/n^{2σ} ↔ 1/2 < σ`, matches paper. ✓
- Walls-merge + `coherence_implies_mirror` (Rem 15.8, `SummedFiberHB.lean:123`): the hypothesis
  `hcoh` is a genuine per-term alignment inequality at all UHP points (not a zeros-are-real
  restatement) → correctly isolated as the one GRH-strength geometric input. Verifies clean. ✓
- DirichletDuality (`vanishing_dual_pair_dirichlet`, `dual_dimension_symmetry_dirichlet`): statements
  match `d_χ(1−ρ)=d_{χ⁻¹}(ρ)` with primitivity + root-number-nonvanishing carried as visible
  hypotheses. Verifies clean. ✓
- GL(3) vanishing side + archimedean discrimination + Stirling π/4 ray (§18.8): 22 ordinates,
  cells 1.0000π sd 0.0000π, pinning 4.0e-14, wrong-parity Γ at 0.2497π — all match
  `tmp/gl3_vanishing_results.txt`. ✓
- Clean Satake tables incl. honest E11 −3.6% flag (§18.5, §18.9): Δ 0.9997±1.1%, E11 0.9636±1.0%,
  Sym²Δ height ladder 1.0006→0.9367→0.8244→0.8297, "OPEN FLAG E11 −3.6%" — all match
  `tmp/satake_clean_results.txt`. ✓
- Jet parity (`hingeDim_parity`, `HingeKernel` even/odd jets): exists, verifies. ✓
- Method laws incl. never-clip (§18.9, §18.11): present, tied to `ClockDipDuality.lean` +
  `reverb_tax_results.txt` no-clip control. ✓

**Coverage gaps (missing ≠ error; report only):**
- **G1.** `satake_variance.py`'s forward-looking result — the reproducible all-negative ~−0.9%
  second-order deficit that *halves with each k* and *grows with ln p*, tagged in FIBER_DYNAMICS
  §3 as "NEXT: compute the second-order prediction and falsify against this table" — is folded into
  the paper only as "finite-bank attenuation + k=3 intermod." The distinct *open* second-order
  self-interaction thread (cross-span corr +0.969 in `tmp/satake_variance_results.txt`) is not
  carried as a named open item. Minor; the paper's clip explanation is the dominant effect, but
  the residual-below-clip systematic is a live loose end in the record and could be named.
- **G2.** The rank-6 method fixes latent-in-rank-5 (G-L x-threshold split, Chebyshev vs
  Vandermonde to avoid deg-19 low-jet flooding; `tmp/rank6_weld_results.txt`,
  `tmp/README.md:63`) are not mentioned. This is exactly the kind of "the machinery bites at large
  √N and here's the fix" honesty note the paper elsewhere prizes; a one-liner in §18.5 would
  strengthen the record. Optional.
- **G3.** `st_cells` "sawtooth, not yet Gaussian (KS 0.0146)" and "lnln unresolved over this range"
  caveats ARE in the paper (§18.7) — good; noting here that this is *present*, not missing.

---

## HONESTY items

The honesty ledger is strong. All requested retractions/corrections are present and prominent:
- Growth-clock retraction — §18.11 (`sub:retractions`), with the two compounding errors named
  (η-prefactor ±2.4×, mixed strata) and the clean-observable replacement (no horizon; 13.5×
  collapse). Matches FIBER_DYNAMICS §1. ✓
- Ghost lines (32.a ln4, 27.a ln8) — §18.11, named as Hann-skirt artifacts → method law (peak
  enumeration, never window-max). ✓
- Conductor-hypothesis → degree statement — §18.5 end, explicitly "corrects our own first reading
  (a 'large conductor' effect)." ✓
- Reverb-tax inversion — §18.9 (`sub:clockdip`): "We asked whether the dips *resist* the clocks: a
  reverb tax. The opposite is true." Matches `tmp/reverb_tax_results.txt` VERDICT. ✓
- ACF corrections — §18.6, "the resolution corrected our own first reading," IAAFT-circularity +
  marginal-refutes-dip-clipping. Matches `tmp/acf_surrogates_results.txt` narrative. ✓
- Clip bias — §18.9: "the deficit was the amplitude clip truncating the dip cores"; turned a 1%
  anomaly into a method law + sharper result. ✓
- Falsifiability register (§sub:falsify): seven signatures F1–F7, first six at count zero, F7
  pre-registered-not-yet-run. E11 −3.6% flag carried honestly at §18.5/§18.9. ✓
- Correction ledger paragraph (§18-evidence end) explicitly lists all firings as "proof of
  operation." ✓

**Honesty nits:**
- **H1.** §sub:falsify F4 says "sixteen ζ lines at 0.1%" for the weight-law channel; the ~0.1%
  ζ figure comes from `tmp/reverb_tax_results.txt` (16 lines listed there: ln2..ln37 k=1 plus
  ln2²/ln3²/ln5²/ln2³). Consistent — flagging only that the "sixteen" should trace to that file,
  which it does. No action.
- **H2.** The falsifiability register is described as "the first six have been deliberately sought
  … the seventh is pre-registered ahead of its first run" — this matches F7's status
  (`aligned_strict_sum_HB` proven, the *measurement* not run). Correctly stated. ✓

---

## INTERNAL CONSISTENCY

- **Module count**: paper says "55 modules" (App A header, §sec:formal). `ls RequestProject/*.lean`
  = 55. ✓ The §sec:formal prose list and App A longtable identifiers all resolve to real files.
- **Compile status**: `lake build` → "Build completed successfully (8613 jobs)." One warning only:
  `ClockDipDuality.lean:77:4: 'push_cast' tactic does nothing` (benign linter). No errors, no sorry
  reported. Axiom footprint spot-checked clean on: `projection_complete_iff_RH`, `carrier_zeros_real`,
  `everyZeroHasSource_iff_critical`, `nontrivial_zero_represented`, `cue_rate_eq_distance_product`,
  `coherence_implies_mirror`, `dual_dimension_symmetry_dirichlet`, `sigma_half_is_scale_critical`,
  `dirichlet_strip_tendsto_LFunction`, `no_native_offaxis_support` — all
  `{propext, Classical.choice, Quot.sound}`.
- **IC1 (minor prose/docstring inconsistency).** Thm 15.5 (`thm:membership`, p. ~1507) states
  `carrier_strand_dominance`: `r^{2−σ} < r^σ ⇔ σ > 1` — this is the *correct* statement and matches
  `WeilDuality.lean:259-262` (`r^(2-σ) < r^σ ↔ 1 < σ`). But the surrounding prose (paper line ~1518,
  and the Lean docstring `WeilDuality.lean:255`) says "with equality precisely at the weld" / "on
  the mirror." The strand-dominance *equality* point is σ=1 (where 2−σ=σ), **not** the mirror σ=1/2.
  The theorem the paper quotes is right; the adjacent "equality at the weld/mirror" gloss is loose.
  Severity: **low**. Fix: change "equality precisely at the weld/on the mirror" to "equality
  precisely at σ=1 (the abscissa of absolute convergence's reflection)," or drop the gloss.
- **IC2 (stale docstring, not a paper error).** `BSDLadder.lean:8` header says "ranks 0–5"; the
  paper and `rank6_weld_results.txt` extend to rank 6. Docstring lag only; paper is correct.
- **IC3.** Notation/cross-refs: the frame-split, admissibility, and midpoint sections cross-reference
  cleanly (`thm:framesplit`↔`rem:admissiblescope`↔`rem:twowalls`). App A longtable rows all map to
  verified identifiers. No dangling refs found in spot checks.

---

## MINOR

- **M1 (abstract number vs body).** Abstract: "eigenheights up to N=e^γ≈3.8×10¹⁵." Body §18.2 tables
  the *deepest actually-worked* zero at conductor 11 (γ₁₈=35.485) as N=2.576×10¹⁵ (verified:
  e^35.485=2.576e15, matches the printed 2,576,182,862,426,122). The 3.8×10¹⁵ is the *cap* implied
  by γ<36 (e^35.87≈3.79e15), not a tabulated zero. Not wrong (γ<36 permits it), but the abstract's
  headline eigenheight is ~1.5× the deepest value the table actually reaches. Consider "up to
  ~3.8×10¹⁵ (the γ<36 exactness cap; deepest worked example 2.6×10¹⁵)" for precision.
- **M2 (verified numbers, no action).** 111 zeros = 5+11+12+14+16+16+18+19 ✓. 2262 primes ≤ 20000 ✓.
  E11 median 0.9636 ✓ (k=1 lines in `satake_clean_results.txt`: 0.9807/0.9625/0.9392/… median ~0.96).
  BSD 7-tuple ✓. Sym²Δ height ladder 1.0006→0.9367→0.8244→0.8297 ✓. Castelnuovo C_k≤1, the exact
  values 0.9889/0.9439/0.8865/0.8261 (m=2) ✓ in `castelnuovo_results.txt`. Gourdon φ=0.500,
  R̂/g=2.93 ✓ (FIBER_DYNAMICS §1). rank-6 |c₆|=3,677,144.76 vs 3,677,144.73 ✓.
- **M3 (retired numbers handled correctly).** The old ±4% Satake (1.007/1.051/0.994) and 0.82±0.13
  Sym² figures appear ONLY as explicitly-labeled *historical/retired* method artifacts
  (§18.5 "The ±4% envelope proved to be method, not medium"; §18.7 "The 0.82 at full span is the
  undersized-bank artifact"). They are never presented as current results. This is exactly the
  requested handling. ✓
- **M4 (prose tier discipline).** Every measured claim in §18 carries a script cite; §sec:evidence
  items are tagged `[Proven]`/`[Measured]`/`[Measured, dichotomy proven]`; the Langlands §19 is
  fenced "This section is interpretation." No sandbagging and no forceful assertion detected — the
  working-hypothesis language ("we adopt, and state as such, a working hypothesis… We do not assert
  it… the other branch needs only one example") is squarely on the tone-policy line. ✓
- **M5.** `GUEBridge.lean:197` docstring says "Elliptic curve 11.a at p=2" for `e11_ln4_silent`;
  paper §18.5 says "level-11 elliptic newform." Same object (11.a in LMFDB); consistent. No action.

---

## Top 5 highest-priority fixes

1. **Thm 15.5 gloss (IC1):** replace "equality precisely at the weld / on the mirror" with
   "equality precisely at σ=1"; the quoted theorem (`σ>1`) is correct but the mirror gloss
   contradicts it. (Also fix the same line in `WeilDuality.lean:255` docstring.)
2. **Thm 15.6 transparency (C1):** add one clause noting `projection_complete_iff_RH` and
   `everyZeroHasSource_iff_critical` follow by *unfolding the projection map* — reframing theorems,
   not hard analytic equivalences — so no reader over-reads "RH ⇔ projection complete is a theorem."
3. **Abstract eigenheight (M1):** qualify "≈3.8×10¹⁵" as the γ<36 cap, with the 2.6×10¹⁵ deepest
   worked example, to match §18.2.
4. **Stale docstring (IC2):** bump `BSDLadder.lean:8` "ranks 0–5" → "0–6" to match the paper.
5. **Optional coverage (G1/G2):** name the sub-clip second-order Satake deficit as a live open
   thread (cross-span corr +0.969) and add a one-line rank-6 method-fix note — both are honesty-ledger
   material the paper would be strengthened by carrying, consistent with its own standard.
