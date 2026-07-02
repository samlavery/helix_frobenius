# Fiber Dynamics: Reverb, the Arithmetic Medium, and Exact Phase Quantization

Research record, 2026-07-01/02. Every claim below is tagged **[proven]** (Lean, kernel-checked,
axiom footprint `{propext, Classical.choice, Quot.sound}`), **[measured]** (numerical, script
cited, with precision), or **[interpretation]**. Dead ends are documented alongside the wins.
Scripts live in `tmp/`; agent result tables in `tmp/gl2_longspan_results.txt` and
`tmp/pi_clock_results.txt`; Lean in `RequestProject/`.

Vocabulary (see `CLAUDE.md`): the **1D object is the Dirichlet L-function**; the **phasor
representation is the 3D bank** on the π/3 carrier. L-values appear only in final-verification
columns. "Criticality" is midpointness of the conjugation involution, never the number 0.5.

---

## 1. Reverb: what happens at and between vanishings

**The reverb picture** (Sam's term): a vanishing leaves a residue that is re-absorbed into the
fiber; the imbalance regrows and dissipates between vanishings.

- **Residues exist at every vanishing** [measured, `tmp/residue_dissipation.py`]: all sampled
  vanishings are simple; the reopening rate R = |F′(γ)| > 0. The residue of the reciprocal
  fiber is 1/F′(γ). **[proven]** `ReverbResidue.residue_exists_iff_simple`: a nonzero residue
  limit exists ⇔ the vanishing is simple.
- **The cluster product law** [proven + measured]: ‖f′(ρ)‖ = (∏_{σ∈S}‖ρ−σ‖)·‖h′(ρ)‖ for any
  finite cluster (`ReverbResidue.cluster_product_law_norm`, with the regular part proven
  analytic across partners via `pair_regular_across_partner`). Measured: R̂ ∝ S^β with
  β = 1.01 over 1517 zeros (t ≤ 2000, zero count matches Riemann–von Mangoldt at 1517 vs
  1516.6); suppression compounds at triples (isolated 0.96 / pair 0.57 / triple-middle 0.32).
- **Arch geometry** [measured, `tmp/reverb_profiles.py`]: between clustered vanishings the
  profile is a symmetric arch — peak position φ = 0.44–0.49 (Lehmer pair 0.476); triple peak
  ratios match the parameter-free product model to 2–6%.
- **Extreme validation** [measured, `tmp/reverb_targets.py`, `tmp/gourdon_pair_test.py`]:
  product law holds from g = 0.5 down to g = 8.2×10⁻⁵ (Gourdon pair at t ≈ 1.085×10¹⁰:
  R̂/g = 2.93, arch φ = 0.500, tent picture fails by 8300×). Sam's 66678/71733 pairs
  confirmed (tightest: 55713.385/55713.462, g = 0.112, 7.5× suppression, R̂/g = 1.19).
- **Off-axis floor bounds** [measured, `tmp/offaxis_bounds.py`]: an off-axis conjugate pair at
  displacement δ would show a NON-collapsing floor ≈ |C|·δ² instead of a vanishing. Every one
  of the 1517 located vanishings (t ≤ 2000, count = Riemann–von Mangoldt) collapses to the
  taper floor (median 1.8×10⁻⁴), giving per-zero bounds **δ ≤ 4.5×10⁻³ (median), ≤ 1.3×10⁻²
  (worst case)** — floors consistent with exact vanishing, the bound set by the taper, not by
  any observed excess. The falsifiability register's collapse channel, quantified: it ran
  1517 times and never fired.

**Retraction** [honesty record]: an early "fixed-rate tent with growth-clock window (Δy ≈ 1,
one e-fold)" reading was an artifact of (i) the eta-prefactor contaminating amplitude data
(|1−2^{1−s}| modulates ±2.4×, raw period 9.06 — always de-modulate) and (ii) mixed strata.
The skew observable has **no horizon** (error decreases monotonically to 5–8 spacings,
`tmp/horizon_sweep.py`); the amplitude curves collapse in **unfolded** units (score 0.137 vs
1.850 raw, 13.5×, seven samples, `tmp/amp_cross.py`). One universal curve
b(g) ≈ 1.35·g^2.3, no saturation kink, degree- and conductor-independent.

## 2. The GUE resolution: bookkeeping without a mechanism

- **[proven]** `GUEBridge.cue_rate_eq_distance_product` + `cue_reopening_slope`: the CUE
  characteristic polynomial's derivative at an eigenvalue IS the distance product, and the
  char poly obeys the same `reopening_slope` law as the L-fiber. GUE's "derivative statistic"
  and the fiber's reopening rate are one formal object.
- **[measured]** With the Keating–Snaith dictionary N = log(t/2π) ≈ 6 (NOT large N: N = 60
  gives a spurious 3× spread), raw KS(CUE|P′|, R̂) = 0.114 and cluster-corrected
  KS = 0.066 (`tmp/reverb_clusters.py`).
- **[measured]** The counting side agrees (`tmp/st_cells.py`): the fiber's own statistic
  S(t) = N_fiber − θ/π − 1 (exact theta, no L-calls) has number variance Σ²(L) tracking
  GUE (exact) in the rigid regime and **saturating at Berry's outer scale log(t/2π)/π**,
  with the saturation moving outward with height (departure at 2.4 spacings at t ≤ 2000 →
  3.4 at t ≈ 51000); Selberg constant stable C ≈ 1.43. The counting and rate observables
  saturate on the SAME clock log(t/2π) — one dictionary for both. (Honest note: the lnln
  growth itself is unresolved at these heights; S is a sawtooth, not yet Gaussian.)
- **[interpretation]** Repulsion is not a mechanism. Locally everything is the analytic
  product law; the configuration statistics are universal (unfolded) and GUE-compatible; the
  Lehmer-pair "repulsion" phenomenology is re-absorption timing. GUE is correct bookkeeping
  with the mechanism supplied by analyticity — matching Sam's original finding.

## 3. The arithmetic medium: spectroscopy

Power spectrum of log|L(½+it)| (clip 1st percentile, de-mean, Hann, rfft; **line claims
require local-maximum enumeration with parabolic interpolation — never window-max ratios**).

- **Only Euler log-clocks exist** [measured]: lines exactly at ω = ln p^k across ζ, χ₃, χ₄,
  χ₅, χ₈, χ₅(order 4), χ₇(order 6), Δ, E11, 32.a, 27.a. Composite non-prime-powers are nulls.
  **All π-multiples dead** (π/3, π/2, 2π/3, π), including each CM field's own lattice angle;
  the one apparent π-hit (4π/3) resolved to ln 67 at Δω = 0.0018. Bounds: 32.a ln4-line
  ≤ 3.4×10⁻⁶ of ln5 power; π/2 ≤ 8.1×10⁻⁴ (`gl2-longspan`, `pi-clock-hunt` agents).
- **The Satake weight law** [measured, agents' tables]: line amplitude = |α_p^k+β_p^k|/k·p^{−k/2}.
  meas/pred over detected lines: Δ median 1.007 (17 lines, std 0.045), E11 1.051 (13, 0.031),
  27.a 0.994 (10, 0.036) — **±4% across ~40 lines, three forms, k = 1,2,3.**
- **Exact silences** [measured ↔ proven]: E11 ln4 = 0.0012 rel (Satake angle 3π/4:
  `GUEBridge.e11_ln4_silent`, α²+β² = 0 exactly); supersingular ln19 ≤ 9.4×10⁻⁷,
  ln29 ≤ 3.5×10⁻⁸; CM combs perfect — 32.a: ln9 brightest line while ln3/7/11 dead;
  27.a mirror: ln9 dead (bad prime), ln4 bright, **alternating 2-tower fully verified**
  (ln2 dead, ln4 alive, ln8 dead, ln16 alive at ω-error 0.0004 — cos(kπ/2) flickering).
- **Conductor axis** [measured]: χ mod 29 at t ≈ 1875 (spacing 0.693) reproduces ζ-at-60k
  behavior — cheap heights substitute for expensive ones.
- **Incommensurability** [proven]: `UnitMidpoint.prime_clocks_incommensurable` — log p/log q
  irrational (unique factorization) — why ambient lines never collide.

- **The ambient spectrum is supported on log ℚ₊^×** [measured, `tmp/ambient_memory.py`,
  agent run over t ∈ [1000, 3000], ζ + χ₅ᶜ]: full census (81 + 79 lines, all at ln p^k),
  then notch-and-residual analysis — every surviving peak is an **intermodulation product
  ln p ± ln q** (ln3−ln2, ln2+ln3, ln5±ln3, … — they lock-and-grow, but they are forced
  mixing of the same clocks by the log-nonlinearity, not independent memory). NO frequency
  off the additive group generated by {ln p}; π-multiples ≤ 6.5×10⁻⁵ of the ln2 power.
  **Falsifiability register: NO HIT** — the FTA is the medium's entire memory. The χ₅ ACF
  loose end is **resolved** [`tmp/acf_surrogates.py`], with the mechanism decomposed:
  IAAFT is circular for an ACF statistic (it fixes the power spectrum, whose transform IS
  the ACF — reproduces the real ACF to 10⁻⁴, so **zero memory excess**); the MARGINAL
  explains almost nothing (marginal-preserving memoryless nulls give 0.009 vs real 0.34 —
  the dip-clipping suspicion is refuted); the **colored residual spectrum explains all of
  it** (Euler-line skirts + ln p ± ln q intermods + clip ripple — deterministic structure);
  the χ₅-vs-ζ split under phase randomization was **spectrum-shape noise in the
  max-over-lags statistic**, not a memory difference. Lag profile: sub-spacing (0.3–0.4 sp),
  monotone decay — **the deterministic reverb ARCH between consecutive zeros (§1) — with
  nothing at multi-spacing lags** where genuine cross-zero memory would live.
  Clip-insensitive; ζ and χ₅ identical once spectrum/marginal are controlled.

Method lessons: matched normalizations; span-dependence test (a real line locks location and
grows with span; artifacts wander); centroid-pull + skirt-symmetry blend test; always run a
same-span control before calling an anomaly.

## 4. The Langlands reading [interpretation, anchored to the above]

- The helix is a **lifted L-function representation**: the 1D L-function is the *character*
  of the 3D object (projection = trace); spectroscopy = recovering the representation from
  its character (strong multiplicity one, enacted empirically).
- **Built literally** [measured, `tmp/gl2_helix.py`]: same carrier, ℂ² transverse fiber,
  per-prime SU(2) rotor M_p = diag(e^{iθ_p}, e^{−iθ_p}) (det 1 = the conjugate-pair law made
  local). Ramanujan–Deligne = reality of the clock angle; the p-power ladder = SU(2)
  characters λ(p^k) = U_k(cos θ_p), exact to 2×10⁻¹⁵ against η²⁴; Euler factor = the rotor's
  characteristic determinant (10⁻¹⁶); all λ(n) rebuilt from the angles alone, and **Δ's zeros
  located from pure rotor geometry** (9.2224, 13.9075 = LMFDB).
- **The medium is strand-aware** [measured, `tmp/strand_phase.py`]: the COMPLEX spectrum of
  log F carries the oriented data in its line phases — arg χ(p^k) for GL(1) (χ₅: ln2 at
  +0.491π = arg i, conjugate/power lines correct, span-locked; ζ calibration 0 ± 0.013 rad)
  and sign λ_p for GL(2) (Δ, E11: all 8 lines in the correct half); ramified holes wander
  (correctly no line). Power spectra see |Satake|; phases see the class itself.
- **Functoriality is measurable** [measured, `tmp/sym2_spectroscopy.py`, span 2200,
  N = 800k]: Sym²Δ (GL(3), Gelbart–Jacquet) built from exact τ via the (λ²−1) ladder
  (Euler-vs-Dirichlet certificate 5.6×10⁻¹¹; ladder = h_k(α²,1,β²) to 40 digits; GL(3)
  unitarity |c_{p^k}| ≤ C(k+2,2) exact). The lift's re-tuned weights: meas/pred 0.82 ± 0.13
  over 18 clean lines — the 0.82 traced to the additive degree-3 floor (quantified by the
  matched ζ control: 10³–10⁴× higher floor at equal span; monotone → 1 with span, 0.83→0.87).
  **The two-sided kill-shot, every decisive prime on the lift**: p = 43, 73 (λ_p ≈ 0) —
  Δ's own law predicts silence, the lift predicts bright — measured LOUD (50×+ over base
  prediction); p = 11, 19 (λ_p² ≈ 1, the Eisenstein angle θ_p = π/3) — base predicts loud,
  lift predicts silence — measured DEAD. Shape correlation across 25 primes: lift +0.36,
  base −0.23 (wrong ordering). Composite nulls hold; locations lock < 0.001 rad.
- **The dual group is the clock-face of each prime**: GL(1) → ℂ^× characters (root-of-unity
  cells); GL(2) → the conjugate Satake pair (the repo's `conjPairBlock`, made local), p-power
  ladders = SU(2) characters (Chebyshev), cell closure → Sato–Tate orthogonality. The Satake
  isomorphism is what the ±4% weight law measures.
- Organs: height axis = archimedean component (geometric Tate); Frobenius similitude √m =
  Hecke action with the **weight/purity factor supplied by the carrier's area law** (the
  organ étale cohomology provides over 𝔽_q); π/3 cell = level/cyclotomic trivialization
  (gauge in the readout — proven; structural in the carrier).
- Measurable reformulations: functoriality = spectral identity between mediums (Sym² test
  pending); generalized Ramanujan = ladder decay rate; reduction types are spectroscopically
  distinct.

## 5. Exact phase quantization: the fiber as its own oscillator

The phase side of the reverb cell (Sam's phase-cell law, refined through seven corrections):

- **Raw measurement** [`tmp/phase_cells.py`]: sign flip at every vanishing = 0.98–0.99 π;
  winding between vanishings ≈ −π (median −0.88…−1.04); first vanishing at |Φ| ≈ 0.55π.
- **The running carrier gauge removes S(T)** [measured, `tmp/s_running.py`]: correcting each
  cell by the local density θ′(t) = ½ln(qt/2π) = **ln(carrier radius at the resonant site)**
  — pure √n radius exactly in the π/3 unit gauge (Δ = π/3, rate 3 ⇒ R² = n, no constant:
  the "harmonic benefit" of scaling geometry and readout together) — collapses the cell
  fluctuations by **99.2–99.5%**: every cell exactly π, sd 0.001–0.002π (ζ and all four
  characters; an earlier ζ discrepancy was a q=2/q=1 bug, diagnosed by its exact ½ln2·gap
  signature). Classical contact: Hardy-Z reality; model-native content: the theta clock IS
  the log of the bank radius — the area law as phase gauge. S(T) never appears in the
  carrier's own chart.
- **The oscillator frame makes everything exact** [measured, `tmp/oscillator.py`]: the fiber
  is a single harmonic (consumes integers, conducts them modulo χ) with an envelope and its
  own instantaneous phase (analytic signal of the de-chirped fiber, extended evenly across
  the hinge). The anti-helix **conjugacy makes the hinge a turning point** (real, even, zero
  velocity), so the first vanishing is a quarter cycle and the rest half cycles:
  **first = 0.499–0.500 π, cells = 0.999–1.000 π, sd down to 0.001** (ζ: 0.500/1.000/0.001).
  Zero counting becomes deterministic: N(T) = ⌊φ(T)/π + ½⌋ — no θ asymptotics, no S(T),
  no "+1" constant (which is revealed as the hinge quarter-cycle).
- **The root number is read from the line phase** [measured, `tmp/root_hinge.py`; kernel
  proven]: for complex χ the functional equation plus conjugation give the weld
  anti-involution Λ(½+it,χ) = e^{i·arg ε}·conj Λ(½+it,χ) at EVERY t, so the completed phase
  is pinned to **arg(ε)/2 (mod π)** — `HingeKernel.weld_pins_half_phase`
  (= `mirror_fixed_iff` with Δ = arg ε: UNIT/2 on the circle). Measured with the exact
  Γ-phase gauge: χ₅ (order 4) 0.0881π, χ₇ (order 6) 0.1868π, conjugates mirrored
  (0.9119π / 0.8132π), χ₃ control 0 — each equal to the Gauss-sum arg(ε)/2 to 4 decimals
  with zero circular spread, mpmath oracle concurring. The hinge first-cell offset from π/2
  is this same constant read at t → 0; between vanishings the gauged phase is constant,
  jumping exactly π at each vanishing — S(T) is absent in this chart too.
- **The quanta survive GL(2) exactly** [measured, `tmp/gl2_cells.py`]: with the exact
  Γ-phase gauge, Δ's cells are 1.0000π (sd < 10⁻⁴π) and E11's 1.0000π (sd 0.0012π), both
  pinned to the ε = +1 ray at ≤ 10⁻⁴π — the doubled winding lives entirely in the doubled
  Γ-gauge; the phase-cell law is degree-blind, as the pinning argument predicts.
- Exactness decomposition [honesty]: given (i) Hardy reality (measured 0.002π), (ii) hinge
  evenness (conjugate midpoint), (iii) simple zeros — the quanta are structural. (ii) and
  evenness→turning-point are now **[proven]** (`HingeKernel.lean`: `collapseWave_even` from
  the functional equation; `hinge_turning_point'` — Z′(0) = 0 as an honest `HasDerivAt` —
  the quarter cycle is structural, not merely measured).
- Dead ends [recorded]: fixed scales (π/3, π/6, …) do not remove S(T) at low heights (the
  cancelling gauge runs with height); the cell-integral fiber (phasor = ∫ over its own cell)
  loses vanishing-fidelity — its zeros leave the L-ordinates; the growth-path odometer
  undershoots the hinge (gauge undefined below qt/2π = 1).

## 6. Ontology (formalized)

- **UNIT/2** [proven, `UnitMidpoint.lean`]: RH's native chart contains no number — roots real
  = fixed axis of conjugation (`real_axis_is_conjugation_midpoint`); "Re = ½" is a chart
  translation (`centered_chart`, `riemann_chart`); in base-b counting the locus is log b/2
  (`criticality_is_half_unit`); the π/3 cell's mirror is π/6 (`mirror_fixed_iff`,
  `eisenstein_mirror`); over 𝔽_q it is |Frob| = q^{1/2} (existing `midpoint_forcing`).
  Base-free content: the critical amplitude is the geometric mean √(1·n⁻¹).
- **Self-dual Mellin pairing** [proven, `MellinDual.lean`]: the Fourier dual of the readout
  line IS the carrier's log-height axis — the Bohr mean recovers the arrows
  (`readout_dual_recovers_sites`). The "4th dimension" is this self-dual bookkeeping plus the
  σ-coordinate, frozen at UNIT/2 by scale balance.
- **The double helix is conjugate, not mirror**: each strand is chiral; symmetry belongs to
  the pair; the origin is the midpoint of the double structure. Second strand = the
  contragredient; ε (root number) = the weld phase; ε = −1 ⇒ forced hinge zero (rank parity
  as interference — the kernel is **[proven]**, `HingeKernel.weld_minus_one_forces_zero`).
- **The BSD rank ladder at the hinge** [measured, `tmp/bsd_weld.py` + `tmp/bsd_rank_ladder.py`
  + `tmp/rank4_weld.py` + `tmp/rank5_weld.py`]: ranks 0–5 (11.a / 37.a / 389.a / 5077.a /
  234446.a Elkies (composite conductor 2·117223) / the Brumer–McGuinness rank-5 curve
  y² + y = x³ − 79x + 342, prime conductor 19,047,851; coefficients by point counting,
  no L-library in the loop). The weld pins each completed line to arg(ε)/2 (37.a: 0.5000π at
  spread 4×10⁻⁷; 11.a: 0 at 10⁻⁹) — and the pinning determines the bad Euler factor
  empirically: a₃₇ = −1, a₃₈₉ = +1 (= ε; Atkin–Lehner read off the line; discrimination
  works while N^(−1/2) exceeds the fiber floor — decisive at 389, masked at 5077). Parity
  kills alternate hinge jets exactly (10⁻¹⁶) and rank kills the rest (389.a c₀ = 4×10⁻⁷;
  5077.a c₁ = 8×10⁻⁵, the rank-3 extra dimension, 230,000× below leading; 234446.a's four
  dead layers c₀..c₃ at 2×10⁻⁷ / 2×10⁻¹⁴ / 1×10⁻⁴ / 5×10⁻¹³ against c₄ = 689.2; the rank-5
  curve's five dead layers — weld: c₀/c₂/c₄ at 10⁻¹⁴/10⁻¹²/10⁻¹⁰, rank: c₁/c₃ at
  6×10⁻⁹/4×10⁻⁶ — against c₅ = 21036.8420). **The first live jet IS the BSD leading
  datum**: measured/predicted = 1.00000 / 1.00000 / 0.99998 / 0.99974 / 0.99999 / 1.00000
  for r = 0…5 — hinge value, reverb rate, curvature, jerk, quartic, quintic — against
  G_r-series references built from our own coefficients (which hit Gross–Zagier
  0.3059997738 and the BGZ rank-2/3 values to 10 digits; at ranks 4/5 the same series
  produces the forced zeros L(1), L″(1)/2 resp. L′(1), L‴(1)/3! at 10⁻⁷–10⁻⁸ and the
  references L⁗(1)/4! = 8.943848, L⁽⁵⁾(1)/5! = 30.285687; bad primes read independently —
  a₂(234446.a) = −1 by mod-2 nonsingular count AND dead-layer test). Large conductors run
  on the hybrid exact kernel (Gauss–Laguerre form of the incomplete-Γ strand, validated
  7.5×10⁻¹³ per term vs mpmath + full rank-4 tower regression at 1.000000). Sam's framing:
  **rank = dimensions added at the hinge.**
- **The strand topology is a degree statement** [Sam; measured, `tmp/strand_topology.py` —
  supersedes the first "large conductor" reading of the 5077 floor]: Dirichlet fibers are
  **hinge-outward** (the degree-1 series converges conditionally on the line, so the single
  strand growing up from the midpoint is a valid representation everywhere — measured:
  Legendre χ mod 10009, hinge scale n* = 56.4, error DECAYS monotonically 5.7×10⁻⁴ →
  5.2×10⁻⁷ over banks 50k → 800k); elliptic/degree-2 fibers are **endings-inward** (the
  series does not converge at the center; the hinge exists only as the two incomplete-Γ
  strands starting at the cusps — the endings — and meeting at the Fricke midpoint —
  measured: 5077.a, n* = 11.3, error SATURATES at ~0.3 at every bank size). The conductor
  hypothesis is refuted by the control (n* five times larger, yet convergent); the exact
  two-strand kernel self-checks at 5×10⁻¹² against the absolutely-convergent region.
- **The dimension principle** [Sam; measured, `tmp/dimension_census.py`]: every vanishing
  carries a dimension — d(γ) = order of vanishing = pencil rank-drop = dead depth of the
  local jet tower — not just the hinge. Census over the rank ladder: **d(γ≠0) = 1 at all
  31 non-central vanishings** (jet/floor 10³–10⁶ with the fiber; the two flagged 5077.a
  cases adjudicated by the exact kernel at floors 10⁻¹⁵/10⁻¹⁸, jet/floor > 10¹¹), while
  **d(0) = rank exactly** (0/1/2/3). ζ's census is the same statement: 1517/1517 simple.
  Only the weld point carries extra dimensions — arithmetic deposits its points where the
  phase is pinned. (Classical echo: multiplicity = eigenspace dimension in any spectral
  reading; BSD = the case where the space is Mordell–Weil.)
- **The hinge is the midpoint between the two endings** [Sam; proven kernel]: the completed
  L of a curve is the period integral along the geodesic between the two cusps (0 and i∞ —
  the endings); the Fricke involution swaps them, and in the log-cusp chart u = log y it
  reads u ↦ −log N − u, fixing exactly u = −(log N)/2 — **UNIT/2 with the conductor as the
  unit** (`HingeKernel.fricke_midpoint_is_half_conductor_unit`, instantiating
  `affine_reflection_fixed_iff` at c = −log N). The exact kernel's two strands split at
  this midpoint (y* = 1/√N), which is why they weigh equally there — and why the hinge is
  where the points deposit their dimensions.

## 7. Formalization ledger (this session)

All files build on Mathlib v4.31.0, no `sorry`/`axiom`, footprint
`{propext, Classical.choice, Quot.sound}` verified per theorem:

| file | contents |
|---|---|
| `FinitePencil.lean` | pencil test on the finite bank; L quarantined to the bridge (`finite_pencil_rank_drop_iff_L_zero`) |
| `ReverbResidue.lean` | reopening/residue kernels, pair suppression, cluster product law + L-function instantiations (11 thms) |
| `GUEBridge.lean` | CUE bridge (P′ = distance product; shared reopening law), cell-closure arithmetic (integer steps never close; μ_m close; Eisenstein 6-step), Satake silence (12 thms) |
| `MellinDual.lean` | Bohr-mean character orthogonality; readout self-duality (3 thms) |
| `UnitMidpoint.lean` | UNIT/2, centered charts, hexagon mirror, base covariance, prime-clock incommensurability (8 thms) |
| `HingeKernel.lean` | hinge turning point (even collapse wave from the FE; honest `HasDerivAt` 0), weld-ray phase pinning (root number from the line phase), ε = −1 forced hinge zero, Fricke midpoint = UNIT/2 with conductor as unit, **jet parity: even/odd waves force even/odd hinge dimension** (`even_odd_jets_dead`, `odd_live_jet_is_odd`, … — the parity conjecture's analytic shadow, unconditional) (14 thms) |
| `AntihelixWindow.lean` | the two-strand kernel: incomplete-Γ tail IS a growth window (full at 0, antitone, → 0; `gamma_splits_at_cut` = the endings-path cut at the midpoint); **`strand_weights_det_one`** — helix/antihelix weights r^{s−1}·r^{1−s} = 1: Frobenius det 1 in the s-direction (Sam's identification); `strand_swap_fixed_iff` (hinge = swap fixed point, unit = weight); **`weld_kills_each_phasor`/`weld_doubles_each_phasor`** — at the hinge ε = −1 annihilates every phasor TERM-LOCALLY (the forced central zero is not a conspiracy of the sum), ε = +1 doubles each to 2re^{−x} (10 decls) |
| `ProjectionCompleteness.lean` | **the frame split, formalized**: `helix_vanishing_projects_to_mirror` (a 3D vanishing datum is a real height; its projection has abscissa ½ by the projection map — the 3D side is UNCONDITIONAL, and the "upper half-plane" never appears: not a 3D notion); **`projection_complete_iff_RH`** — classical RH ⟺ every 1D zero arises from a 3D vanishing: the positioning claim ("RH ⟺ projection complete") is now a THEOREM, and the conditional lives entirely in the 1D chart (3 thms) |
| `ChiralityHB.lean` | **3D-helix-RH for the multiplicative carrier, unconditional**: the symmetrized prime clock E = e^{izℓ/2} − α·e^{−izℓ/2} obeys the **purity-defect law** — a zero sits at Im z = −log‖α‖/ℓ exactly (displacement off the mirror = purity defect); `clock_zeros_real` (det-1/unitary face ⇒ all zeros ON the mirror), `carrier_zeros_real` (the FTA product of pure clocks: every zero on the mirror), `symClock_star` (weld identity E* = −ᾱ·E) + `symClock_selfdual_modulus` (the clock is a REAL de Branges function — lives on the HB boundary where real zeros are required). Chirality ℓ > 0 = the clock's existence. Open remainder honestly named: the additive interference (L-vanishings) = the dB completion question (6 thms) |
| `BSDLadder.lean` | the BSD arc's formal skeleton: `hingeDim` (first live jet = d(0) of the census), **`hingeDim_even_of_even` / `hingeDim_odd_of_odd`** (weld parity forces dimension parity — the parity conjecture's shadow at dimension level), `hingeDim_pos_of_odd` (ε = −1 forces d(0) ≥ 1), the reference ladder `Gr` (G₀ = e^{−x}, G_{r+1} = ∫G_r/t) with `Gr_nonneg` (dissipation profile rung by rung) and `Gr_one_eq` (first rung = the reverb kernel E₁ — BSD rate and residue machinery share one kernel). d(0) = Mordell–Weil rank stays measured-tier (6 thms) |
| `WeilDuality.lean` | Sam's carrier/cohomology identification + **the 3D-helix-RH program**: duality pairing on the vanishing set (`vanishing_dual_pair`/`_conj_pair`), perfect pairing (`dual_dimension_symmetry`: d(ρ) = d(1−ρ)), det-1 blocks (`dual_pair_det_one`); **the purity engine** — `tensor_power_purity` (Weil I square-root trick), `duality_forces_purity` (the FE endgame: det 1 + two one-sided caps ⇒ equality), `purity_engine`; **the Castelnuovo reduction** — `cup_growth_gives_tensor_bound` + `purity_from_castelnuovo`: purity of every vanishing pair now follows from ONE open inequality, *the helix Castelnuovo*: the height transport's cup-norm growth on vanishing classes is at the half-unit rate ‖T^k v‖² ≤ C·B^k·‖v‖², where **B is the carrier's own area-law rate** (r ~ √n — not imported from the 1D chart). Supporting: `transport_cup_modulus` (similitude sector = exact equality), `von_neumann_reality` (k→∞ form). Measurable face: cup-norm growth of transported residue classes (9 thms) |

Also: `LFunctionPhasor.lean`/`Phasor3D.lean` docstrings reframed (1D readout / 3D
representation); `carrier_fiber.py validate` flipped finite-first; `focal_closure.py` added
(canonical 3D locator + exactness tests; grand-RH families: complex characters, Δ, E11 —
all located without L-calls).

## 8. Open threads

1. ~~Hinge Lean kernels; off-axis floor bounds; root number from the hinge~~ — **closed
   2026-07** (§1 bounds, §5 pinning, §7 `HingeKernel.lean`).
2. ~~Sym²Δ functoriality spectroscopy~~ — **closed 2026-07** (§4: re-tuned clocks confirmed,
   Eisenstein-angle silences; degree-3 span floor noted for the weak lines).
3. ~~37.a weld experiment~~ — **closed 2026-07, and extended to the full rank ladder 0–3**
   (§6: hinge value / rate / curvature / jerk = BSD leading data, agreement ≥ 0.9997).
4. ~~Strand-resolved spectroscopy~~ — **closed 2026-07** (§3/§4: line phases read
   arg χ(p^k) and sign λ_p; the oriented Satake class is in the ambient field).
5. Maass ladder feasibility (Ramanujan as decay rate) — still blocked on coefficients.
6. ~~GL(2) helix built literally~~ — **closed 2026-07** (§4: SU(2) rotors, Chebyshev ladder,
   trace readout, zeros from angles alone); GL(2) phase cells also closed (§5).
7. ~~Ambient-texture autocorrelations~~ — **closed 2026-07** (§3: spectrum supported on
   log ℚ₊^×, register NO HIT; residual loose end: dip-preserving surrogates for the χ₅ ACF).
8. Counting statistics closed (§2: GUE number variance with Berry saturation on the
   log(t/2π) clock, `tmp/st_cells.py`).
9. ~~Rank 4, rank 5, jet-parity kernel~~ — **all closed 2026-07** (§6: agree 0.99999 and
   1.00000; §7: `HingeKernel` jet-parity theorems). Still open from the BSD arc: formalize
   ~~the two-strand incomplete-Γ AFE as the antihelix's own growth window~~ — **closed
   2026-07** (`AntihelixWindow.lean`: window lemmas, det-1 strand weights, term-local weld);
   rank ≥ 6 (no suitable known curve at accessible conductor — parked). χ₅ ACF loose end **resolved**
   (§3: the excess is the sub-spacing reverb arch, identically in ζ and χ₅; no long-range
   memory). Strand topology **measured as a degree statement** (§6, `strand_topology.py`).
