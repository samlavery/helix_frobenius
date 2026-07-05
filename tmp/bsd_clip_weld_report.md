# The clipped-helix picture: clip, weld, root number, rank, crossings

Report for the four-question investigation. Every number below comes from a script actually
run in `/Users/samuellavery/work/helix_frobenius/tmp/` or a Lean theorem read in
`/Users/samuellavery/work/helix_frobenius/RequestProject/`. Tiers: **PROVEN** (named Lean
theorem, repo invariant: axioms ⊆ {propext, Classical.choice, Quot.sound}, no sorry/axiom),
**MEASURED** (script + numbers), **HYPOTHESIS**.

## The model recap (what "clip" and "weld" mean here)

The completed L of a curve of conductor `N` is the two-strand incomplete-Gamma kernel
(`AntihelixWindow.lean`, exact-checked in `strand_topology.py` to 5e-12 at s=2):

    Λ(s) = Σ aₙ [ rₙ^s · Γ(s, xₙ)  +  ε · rₙ^{2−s} · Γ(2−s, xₙ) ],   xₙ = 2π n/√N,  rₙ = √N/(2π n),  rₙ xₙ = 1.

- **helix strand** = the `rₙ^s Γ(s,xₙ)` term; **antihelix strand** = the `ε rₙ^{2−s} Γ(2−s,xₙ)` term.
- `Γ(s, xₙ)` is a **growth window**: full weight `Γ(s)` at the cut `xₙ=0`, monotone dying to 0
  (PROVEN: `AntihelixWindow.upperGamma_one` [Γ(1,x)=e^{−x}], `upperGamma_antitone`, `upperGamma_tendsto_zero`).
- The phasor bank reads `s = ½ + it` in **analytic** normalization (λₙ = aₙ/√n, magnitude n^{−½});
  the strand file uses **arithmetic** normalization `s = 1 + it` (weld at s=1). These differ by a ½ shift.

---

## (A) CLIP ↔ CONDUCTOR — clip-length ∝ √N (the analytic conductor), NOT log N

**Finding.** The finite conductor clips each strand to a finite phasor bank. What is clipped is
the **phasor count / arclength range**; the two legs both end at the phasor index where the
incomplete-Gamma window closes (`xₙ ≳ 1`, i.e. `n ≳ √N/2π`), and meet at the weld (`xₙ→0` ⇔ the center).
The clip length scales as **√N** — the analytic conductor — not log N and not N.

**MEASURED** — `tmp/clip_conductor.py` → `tmp/clip_conductor_results.txt`:
- Effective live-phasor count `n_eff(1%)` = # phasors with weld window `e^{−xₙ} ≥ 0.01`.
  Across `N = 10 … 10⁸` (7 decades), `n_eff/√N = 0.73294` **constant to 5 digits**;
  log-log fit `n_eff ~ 0.7329·N^{0.5000}` (exponent 0.5000 = pure √N).
- Weld arclength `Σ (√N/πn) e^{−2πn/√N}` has closed form `(√N/π)·(−ln(1−e^{−2π/√N}))`
  (matched to machine precision at N=10⁴,10⁶,10⁸), asymptotically `(√N/2π)·ln N` — leading power
  still ½, with a slow log modulation.
- Real conductors on the same law (`n_eff/√N = 0.73294` identically): 11a→2.43, 37a→4.46,
  49a-CM→5.13, 389a→14.46, 5077a→52.22 phasors; the literal `xₙ>45` kernel cutoff used in
  `bsd_weld.py` gives `n_max = 45√N/2π` (11a→24, 5077a→510).

**MEASURED** — `tmp/clip_conductor_real.py` → `..._results.txt` (point-counted aₙ, validated
Hecke-multiplicative + Deligne-bounded; CM curve 27a passes the a_p=0 for p≡2 mod 3 supersingular
signature). Weighting by the actual coefficients |λₙ|, the strand mass's 99%-cutoff sits at
`clip99/√N ≈ 0.60–0.77` (11a 0.60, 27a 0.77, 37a 0.66, 389a 0.66, 5077a 0.60) — the bulk lives
inside the same √N-scaled window. (The 90% cutoff is noisier, CV 0.40, because the coefficient-
weighted mass concentrates at very small n where integer discretization dominates; the clean,
oracle-free statement is the geometric `n_eff ∝ √N`.)

**OPEN vs CLIPPED (the degree distinction)** — MEASURED, `tmp/strand_topology.py`: the single
hinge-**outward** strand (plain series with the Γ-prefactor) error vs bank size:
- degree-1 Dirichlet χ mod 10009: DECAYS `5.7e−4 → 1.0e−5 → 2.1e−6 → 5.2e−7` (converges on the
  line → **OPEN** helix, valid single outward strand);
- degree-2 elliptic 5077a: SATURATES at a bank-independent floor `0.70, 0.27, 0.36` (diverges on
  the line → **CLIPPED**: exists at the hinge only as the two endings-inward strands).

**Relation clip-length = f(N):** `clip = c·√N`, `c = x_cut/2π` (MEASURED, exponent 0.5000). The
window structure that forces it is PROVEN (`upperGamma_*`); the exact constant is the window
threshold, not a theorem.

**Falsification register (A):** tested `clip ∝ log N` — FAILS: `n_eff/log N` varies ~6× across the
sweep (not constant), while `n_eff/√N` is constant to 5 digits. Tested `clip ∝ N` — FAILS: log-log
exponent is 0.5000, not 1. Tested whether the coefficient-weighted clip breaks √N — it does not
(clip99/√N stays 0.6–0.77), but it is noisier than the geometric measure (reported honestly).

---

## (B) ORIGIN ↔ s NORMALIZATION — the weld is the FE involution's fixed point; its coordinate is gauge

**Finding.** The meeting point of the two legs is the **fixed point of the functional-equation
involution**, and its numeric coordinate is pure gauge (`UnitMidpoint.lean`: "criticality is
midpointness of an involution; the coordinate is the chart"). It is **UNIT/2 for every unit c**
(PROVEN: `UnitMidpoint.affine_reflection_fixed_iff` — `c − x = x ↔ x = c/2`):

    chart                       involution          unit c      weld coordinate
    centered / Riemann  t       t ↦ −t                 0         t = 0      ← Sam's instinct
    analytic  s                 s ↦ 1−s                1         s = 1/2
    arithmetic / motivic  s     s ↦ 2−s                2         s = 1
    Fricke cusp  u = log y      u ↦ −log N − u      −log N       u = −(log N)/2

**Sam's instinct "the weld might be s=0" is CORRECT — in the centered/Riemann chart** (unit 0),
where the involution is `t ↦ −t` and the RH statement is "roots are real" with no number in it.
The weld is `t = 0`, the fixed axis of complex conjugation. PROVEN: `UnitMidpoint.riemann_chart`
(`t = −i(ρ − ½)` real ⇔ Re ρ = ½), `real_axis_is_conjugation_midpoint` (conj z = z ⇔ Im z = 0).

**MEASURED** — `tmp/weld_normalization.py` → `..._results.txt`:
1. The helix and antihelix strands are **equal term-by-term exactly at the arithmetic weld s=1**
   (helix−anti = 0.0 at s=1; ±0.075 at s=1±0.05; ±0.63 at s=1±0.4). At the weld each strand =
   `r·e^{−x}` (`upperGamma_one`), so ε=−1 KILLS (→0) and ε=+1 DOUBLES (→2r e^{−x}). This is
   `AntihelixWindow.strand_swap_fixed_iff` (2−s=s ⇔ s=1), `weld_kills_each_phasor`,
   `weld_doubles_each_phasor` — all PROVEN.
2. Centered translation `t = −i(s − c/2)` is real ⇔ Re s = c/2, verified for c=0,1,2 (`centered_chart`).

**Reconciliation with the geometric origin.** The candidate "geometric origin y=0 / N=0 (spiral
base)" conflates two DIFFERENT points, and neither `N=0` picture is the weld:
- The **spiral arclength origin N=0** is at `Z = e^y → 0`, i.e. `y → −∞` (radius→0, arclength→0 in
  `ClosedForm.arclength`). MEASURED: at y=−6, Z=0.0025, N≈0.003. This is NOT the weld.
- The **weld** is the **ordinate origin t=0** (`y = Im s = t`), where the readout head sits at
  `Z = e^0 = 1` (one phasor, N≈O(1)). MEASURED: at y=0, Z=1, N≈3.4. This is `s=½` analytic = `s=1`
  arithmetic.
- So the correct normalization: **weld = the ordinate origin t=0** = the FE fixed point, `s=½`
  (analytic) = `s=1` (arithmetic) = `u=−(logN)/2` (Fricke), = "0" in Sam's centered chart. It is
  emphatically **not** the spiral base N=0 (that is Z=0, y=−∞), and **not** `s=0` in the standard
  analytic/arithmetic s-plane (that is the strip edge / trivial-zero region, not the center).

**Falsification register (B):** tested "weld = spiral base N=0" — FAILS: N=0 is at Z=0 (y=−∞), the
weld is at Z=1 (t=0). Tested "weld = literal s=0 in the analytic plane" — FAILS: s=0 analytic is
Re s=0, the edge of the critical strip, symmetric partner of s=1 under s↦1−s, not the fixed point.
The self-consistent reading (Sam's, in the right chart) survives: weld = 0 in the centered variable.

---

## (C) WELD ↔ ROOT NUMBER ↔ CENTRAL RANK ↔ BSD — one mechanism, verified ranks 0–3 + CM

**Finding.** The weld's focal cancellation encodes all three, and it **is** the same mechanism as
`BSDClocks.rank_is_dc_residue`. The chain:

- **(i) root number ε = the weld sign.** `Λ(½+it) = ε·conj Λ(½+it)` pins the line phase to the
  ray `arg(ε)/2` (PROVEN: `HingeKernel.weld_pins_half_phase` = `UnitMidpoint.conj_fixed_iff`).
  ε=−1 makes the two equal strands cancel term-by-term → forced central zero (PROVEN:
  `weld_kills_each_phasor`, `weld_minus_one_forces_zero`); ε=+1 doubles them → turning point
  (PROVEN: `weld_doubles_each_phasor`, `hinge_turning_point` [Z′(0)=0 from `collapseWave_even`]).
- **(ii) central rank r = order of central vanishing = the DC residue** of the log-derivative
  (PROVEN: `BSDClocks.rank_is_dc_residue`: `F=(s−c)^r·G ⟹ (s−c)F′/F → r`). PARITY is the weld's
  extra bit: ε=+1 ⇒ Λ even in t ⇒ ODD jets structurally dead ⇒ r EVEN; ε=−1 ⇒ Λ odd ⇒ EVEN jets
  dead ⇒ r ODD (PROVEN: `HingeKernel.even_live_jet_is_even`/`odd_live_jet_is_odd`,
  `BSDClocks.bsd_rank_parity_even`/`_odd`).
- **(iii) BSD leading datum L^{(r)}(center)/r! = the first LIVE jet = G(center)** (PROVEN:
  `BSDClocks.leading_jet_extraction`, `first_jet_eq_deriv`); |Ш| lands from it within ½ (PROVEN:
  `jet_measurement_sound`). Every actual L-function is an instance (PROVEN: `model_form_exists`,
  finite r + G(c)≠0 by modularity[cited]).

**Yes — the weld cancellation is the same mechanism as `rank_is_dc_residue`.** The weld sets the
**parity** of the first live jet (via ε); the DC residue reads its **order** r; leading-jet
extraction reads its **value** = L^{(r)}/r!. Three readings of one factorization `(s−c)^r·G`.

**MEASURED** — `tmp/bsd_rank_ladder.py` (fresh run) — the jet tower at the weld, ranks 0–3, exact
double-ended incomplete-Gamma kernel; `agree` = ratio of the fitted first-live jet to
`(√N/2π)·L^{(r)}(1)/r!`, `lit` = ratio to literature:

    curve   r  ε(ray)      jet tower |c0..c3|                  first-live |c_r|   agree      lit
    11.a    0  +1(0.000π)  1.34e-1 9.9e-18 1.7e-2 5.8e-16       0.13399           1.00000    1.0000
    37.a    1  −1(0.500π)  9.5e-18 2.96e-1 4.4e-16 5.6e-2       0.29624 (=Λ′(0))  1.00000    1.0000  [Gross-Zagier L′(1)]
    389.a   2  +1(1.000π)  4.2e-07 9.8e-16 2.38e+0 4.6e-15      2.38345           0.99998    1.0000  [L″(1)/2!]
    5077.a  3  −1(0.502π)  8.0e-17 8.5e-05 4.2e-15 1.96e+1     19.63454           0.99974    1.0000  [L‴(1)/3!]

The jet tower LITERALLY shows the double kill: alternate jets `~1e-15…1e-18` (parity-dead by the
weld) AND the sub-rank live jets `~0` (rank-dead by the arithmetic), with the first survivor at
order r = the BSD leading datum. "rank = dimensions added at the hinge."

**MEASURED** — `tmp/bsd_weld.py`: 37a (ε=−1) forced central zero |Λ(½)|=6.7e−5 (2.4e−4 of scale),
reverb rate |Λ′(½)|=0.29562 vs (√37/2π)L′(1)=0.29624 (agree 0.998, Gross-Zagier L′(1)=0.30600);
11a (ε=+1) turning point |Λ(½)|=0.13399 vs (√11/2π)L(1)=0.13399 (agree 1.000002), hinge slope 2e−6.

**MEASURED** — `tmp/weld_rank_census.py` (independent CM control): 27a (CM by Q(√−3), N=27, rank 0):
ε=+1 (ray at 1.000π, circular spread 8.8e−14), r=0 (even) — parity law OK; jet tower c0=0.487
(live), c1=4.2e−14 (parity-dead odd jet), c2=0.103 (live even jet), c3=8.5e−13 (parity-dead). The
mechanism reproduces on a CM curve of a different reduction type.

**Falsification register (C):** tested parity violation (an ε=+1 curve with odd rank, or ε=−1 with
even rank) — NONE found across 11a/27a/37a/389a/5077a (ranks 0,0,1,2,3; ε +,+,−,+,−; parity law
holds in all 5). Tested whether the first live jet fails to be the BSD datum — agreement is
1.00000/1.00000/0.99998/0.99974 (worst 0.026% at rank 3, a bank-truncation effect). Tested whether
the ε read from the geometric ray disagrees with Atkin-Lehner ε — agrees in all cases.

---

## (D) IS THE CROSSING SPACING PROVABLE? — YES, reduced to a clean statement; core input already PROVEN

**Finding.** The measured spacing (first crossing at accumulated fiber-phase π/2, every subsequent
at π) is **provable**, reducing to "the zeros of a positive-envelope cosine that starts at an
extremum are at φ = π/2 + kπ." The load-bearing input is **already PROVEN**.

**The reduction (proof sketch):**
1. `Z(t) = Λ(½+it)` is REAL and EVEN in t — PROVEN: `HingeKernel.collapseWave_even` (from the FE
   `Λ(1−s)=Λ(s)`; self-dual ε=+1). Evenness ⇒ `Z′(0)=0` — PROVEN: `HingeKernel.hinge_turning_point`
   (`even_deriv_zero`). **The hinge is an EXTREMUM, not a crossing.** This is exactly why the first
   crossing is a QUARTER cycle (π/2) out, not a half.
2. Hardy form `Z(t) = A(t) cos φ(t)`, A>0 the envelope, φ the accumulated fiber-phase (analytic-
   signal phase / completed argument / Riemann-Siegel θ). Evenness forces `φ(0) ≡ 0 (mod π)`: the
   oscillator starts at an extremum. ("Each conjugate leg contributes π/2 to the origin" = the two
   FE legs are conjugate; the completed argument is stationary at the fixed point.)
3. Zeros of cos are at `φ = π/2 + kπ`. With φ(0)=0 and φ monotone ⇒ first zero at φ=π/2 (extremum
   →zero = quarter cycle), consecutive zeros at Δφ = π (half cycles). QED for the spacing.
4. **Argument principle:** the completed argument advances by exactly π at each simple real zero
   (sign change of the Hardy function), so `N(T) = ⌊(φ(T)−φ(0))/π + ½⌋` — the +½ being the even/
   extremum start = the π/2 first offset. This IS Riemann–von Mangoldt / Backlund counting via
   arg Λ; each crossing = one π of phase.

**MEASURED** — `tmp/crossing_spacing_proof.py` → `..._results.txt`:
- Steps 1–3, on de-chirped real fibers (zeta, χ4, χ8): `φ(0)/π` is an integer (8, 14, 18 —
  extremum), first crossing at `0.500·π`, median cell `1.000·π`. Matches the prediction exactly.
- Step 4, argument-principle count `N(T)=⌊(φ(T)−φ(0))/π+½⌋` vs actual crossings ≤ T: **matches to
  the integer in all 9 test points** (zeta: 2,5,8; χ4: 5,10,14; χ8: 7,13,19 — all OK).
- Exact cross-check on completed zeta via mpmath: `Λ(½)=−3.977` (extremum ≠ 0), `Λ′(0)=0.0e0`
  (turning point), even to 0.0e0, first zeros 14.13/21.02/25.01 (= ζ zeros). Gaps in t are NOT
  constant (14.13, 6.88, 3.99) — constant only in PHASE φ, confirming it is the phase, not t, that
  is quantized in π.
- This also reproduces the older `oscillator.py` result (first 0.499–0.500·π, cell 0.999–1.000·π).

**Provable? Yes.** The one nontrivial analytic input (φ(0)=0, i.e. the hinge is an extremum) is
already a Lean theorem (`hinge_turning_point`, from `collapseWave_even`). The remaining "cos has
zeros at π/2+kπ, spaced π" is elementary and Lean-able (a positive-envelope cosine with φ(0)=0,
φ monotone). The argument-principle statement `N(T)=⌊(φ(T)−φ(0))/π+½⌋` is the standard completed-
argument zero count; formalizing it needs the winding/argument machinery (out of scope, not
required). **Bonus Lean target:** a clean lemma `zeros_of_pos_envelope_cosine_from_extremum`.

**Falsification register (D):** tested whether the first crossing could be π (half cycle, i.e. the
hinge a crossing not an extremum) — FAILS: `Λ′(0)=0` exactly, `Λ(½)≠0`, first crossing is 0.500·π.
Tested whether the spacing is constant in t (rather than in phase) — FAILS: t-gaps are 14.13, 6.88,
3.99 (decreasing), only the phase increments are constant (π). Tested the argument-principle count
with the naive `φ(T)/π−½` (no φ(0) subtraction) — FAILS (off by the analytic-signal phase offset);
the correct `(φ(T)−φ(0))/π` lands to the integer. χ5 shows a large cell-spacing std (0.43 in
`oscillator.py`) from a near-degenerate close pair — a resolution artifact, not a spacing violation.

---

## Scripts (all in `/Users/samuellavery/work/helix_frobenius/tmp/`, co-located with `bsd_weld.py`)

- `clip_conductor.py` (+ `_results.txt`) — (A) geometric clip law, n_eff ∝ √N exponent 0.5000. [pre-existing, run fresh]
- `clip_conductor_real.py` (+ `_results.txt`) — (A) point-counted aₙ, CM validation, actual-mass clip. [new]
- `strand_topology.py` — (A) open (deg 1) vs clipped (deg 2) degree distinction. [pre-existing, run fresh]
- `weld_normalization.py` (+ `_results.txt`) — (B) strand equality at s=1, chart translations, weld≠spiral base. [new]
- `bsd_rank_ladder.py`, `bsd_weld.py` — (C) jet tower ranks 0–3, forced-zero / turning-point. [pre-existing, run fresh]
- `weld_rank_census.py` (+ `_results.txt`) — (C) CM control 27a + parity ladder. [new]
- `crossing_spacing_proof.py` (+ `_results.txt`) — (D) π/2-then-π reduction + argument-principle count. [new]
- `oscillator.py` — (D) original crossing-spacing measurement. [pre-existing, run fresh]

## Lean theorems cited (all in `RequestProject/`, repo invariant: no sorry/axiom, standard axioms)

- `AntihelixWindow.lean`: `upperGamma_one/antitone/tendsto_zero`, `gamma_splits_at_cut`,
  `strandPair`, `strand_swap_fixed_iff`, `strand_weights_det_one`, `weld_kills_each_phasor`,
  `weld_doubles_each_phasor`.
- `HingeKernel.lean`: `collapseWave_even`, `hinge_turning_point`, `weld_pins_half_phase`,
  `weld_minus_one_forces_zero`, `even_live_jet_is_even`, `odd_live_jet_is_odd`,
  `fricke_midpoint_is_half_conductor_unit`.
- `BSDClocks.lean`: `rank_is_dc_residue`, `leading_jet_extraction`, `first_jet_eq_deriv`,
  `jet_measurement_sound`, `bsd_rank_parity_even/_odd`, `model_form_exists`.
- `UnitMidpoint.lean`: `affine_reflection_fixed_iff`, `centered_chart`, `riemann_chart`,
  `real_axis_is_conjugation_midpoint`, `conj_fixed_iff`, `criticality_is_half_unit`.
- `FrobeniusSimilitude.lean`: `reflection_fixes_iff`, `scaleBalanced_iff`.
- `ClosedForm.lean`: `arclength`, `arclength_closed_form`, `Nindex`, `Delta` (=π/3), `spinAngle`.

## Two-question discipline check

None of (A)–(D) assumes RH/GRH, and none is circular. (A) clip=√N is a window fact. (B)/(C) the
weld/rank readings are functional-equation + jet algebra. (D) reduces to an elementary cosine
statement whose one analytic input is already proven. All are valid targets; the results are tiered
exactly to the evidence.
