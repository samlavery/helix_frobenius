# Clip / Weld / Crossing — four questions on the clipped elliptic helix

Scope discipline: every finding tiered PROVEN (a named Lean theorem in this repo, whose
files carry the docstring scope-line "no `sorry`, no `axiom`, no zero-location claims"),
MEASURED (a script + actual numbers), or HYPOTHESIS. Nothing here assumes or proves RH/GRH.
The one RH-adjacent item (D, spacing rigidity) is isolated as an explicit open piece.

Scripts (all in `tmp/`): `clip_conductor.py` (A), `origin_normalization.py` (B),
`bsd_weld.py` + `bsd_rank_ladder.py` + `jet_census.py` (C), `oscillator.py` +
`crossing_spacing.py` (D).

---

## (A) CLIP ↔ CONDUCTOR — what N clips, and the law

**Finding.** The conductor does **not** clip a height range in `t` (the completed
`Λ(½+it)` runs over all real `t`). What is clipped is the **fiber**: the phasor bank /
arclength direction. The mechanism is the incomplete-Gamma growth window in the
double-ended kernel
`Λ(s) = Σ aₙ[ rₙ^s Γ(s,xₙ) + ε rₙ^{2−s} Γ(2−s,xₙ) ]`, with `xₙ = 2πn/√N`,
`rₙ = √N/(2πn)`, `rₙxₙ = 1`. `Γ(s,xₙ)` is full-weight at `xₙ=0` and dies monotonically to
0 (`AntihelixWindow.upperGamma_zero / upperGamma_antitone / upperGamma_tendsto_zero`), so
phasor `n` is "open" while `xₙ = O(1)` and clipped off once `xₙ ≫ 1`. Both legs (the `n^s`
helix strand and the `ε·n^{2−s}` antihelix strand) end at the **same** phasor index
`n_max` where the window closes, and they meet at the weld as `xₙ → 0` (the center).

**The law (MEASURED, `tmp/clip_conductor.py`):** the live-phasor count is **exactly √N-scaled**.

| N | √N | n_eff(1% window) | n_eff/√N |
|---|----|----|----|
| 10 | 3.16 | 2.318 | 0.73294 |
| 10³ | 31.62 | 23.177 | 0.73294 |
| 10⁶ | 1000 | 732.94 | 0.73294 |
| 10⁸ | 10000 | 7329.4 | 0.73294 |

`n_eff/√N` is a **constant** (`= x_cut/2π`) over 7 decades. Log-log fit:
`n_eff ~ 0.7329·N^0.5000` — exponent **0.5000**, i.e. clip-length = `c·√N`, **not** `log N`,
**not** `N`. Real conductors sit exactly on the line (37a, 389a, 49a-CM, 5077a, 11a all give
`n_eff/√N = 0.73294`). The pure-carrier *arclength* (with `|aₙ|=1`) carries a slow log
factor on top: `arclen = (√N/π)·(−ln(1−e^{−2π/√N}))` (closed-form verified to full precision)
`~ (√N/2π)·ln N` — leading power still ½, log-modulated.

**Where √N comes from / tier of the law itself.** √N is the analytic-conductor scale of the
weight-2 level-N functional equation, and it is the multiplicative assembly of the per-prime
similitudes `‖frobeniusMultiplier θ p‖ = √p` (`FrobeniusSimilitude.norm_frobeniusMultiplier`,
`BSDClocks.clockTraceB` faces at radius `√B`, `B=p`). So the **√N clip is the area law**
(`FrobeniusSimilitude.scaleBalanced_iff`, the σ=½ area law). Tier: the window structure is
PROVEN (`upperGamma_*`); the numeric exponent 0.500 is MEASURED; its identification with the
conductor area-law is a structural HYPOTHESIS grounded in the proven per-prime √p similitude.

**Falsification register (A).** Disconfirmed if `n_eff/√N` drifted with N (it is flat to
5 digits), if the fitted exponent were 0 (log) or 1 (linear) rather than 0.5000, or if a
curve fell off the √N line. Hits: **zero**.

---

## (B) ORIGIN ↔ s-NORMALIZATION — which point is the weld (the genuinely open one)

**Finding — Sam's instinct is CONFIRMED.** The weld is the **central point**,
`s = 1` (arithmetic normalization) `= s = ½` (analytic) `= t = 0`. It is **not** the
geometric spiral origin.

The weld is defined kernel-side as the point where the helix strand `rₙ^s Γ(s,xₙ)` and the
antihelix strand `rₙ^{2−s} Γ(2−s,xₙ)` weigh equally for every phasor — the fixed locus of
the strand swap `s ↦ 2−s`. MEASURED (`tmp/origin_normalization.py`): the balance ratio
`B(Re s) = |rₙ^s Γ(s,xₙ)| / |rₙ^{2−s} Γ(2−s,xₙ)|` equals **1 identically on `Re s = 1`**, for
every phasor (`n=1,3,10`), and `≠1` off it (0.30 at Re s=½, 10.97 at Re s=2 for `n=1`). This
is exactly `AntihelixWindow.strand_weights_det_one` (`r^{s−1}·r^{1−s}=1`) made numeric.

**The correct normalization, stated explicitly.** Four charts, one point (all PROVEN):

| chart | involution | fixed point | Lean theorem |
|---|---|---|---|
| arithmetic FE | `s ↦ 2−s` | `s = 1` | `AntihelixWindow.strand_swap_fixed_iff` |
| analytic FE | `s ↦ 1−s` | `s = ½` | `FrobeniusSimilitude.reflection_fixes_iff` |
| Riemann chart | `t = −i(ρ−½)` | `Re ρ = ½` | `UnitMidpoint.riemann_chart` |
| Fricke geodesic | `u ↦ −ln N − u` | `u = −(ln N)/2` | `HingeKernel.fricke_midpoint_is_half_conductor_unit` |

They are the same UNIT/2 midpoint in different gauges (`UnitMidpoint.affine_reflection_fixed_iff`:
`c−x=x ↔ x=c/2`, unit `c` = the reflection unit, = the conductor in the Fricke geodesic where
`y = e^u = 1/√N`). The arithmetic `s=1` and analytic `s=½` differ only by the shift `s = 1+it`
vs `s = ½+it` — the same central `t=0`.

**The geometric origin is a different point.** `ClosedForm.numberSite_zero` puts the N-count=0
site at `(0,0,0)` and `fiber_origin` makes the fiber there empty — this is the `y → −∞` base
of the carrier where **no phasor has entered yet** (the start of growth), not the strand-balance
point. The weld sits at the center where **all** live phasors have entered and the two legs
weigh equally. So candidate (i) is refuted; candidates (ii)+(iii) coincide and are correct;
(iv) `s=0` is the FE-mirror of `s=2`, an edge, not the center.

Tier: PROVEN (the five theorems above are exact and unconditional) + MEASURED (the balance
ratio `B(1)=1`).

**Falsification register (B).** Disconfirmed if `B(Re s)=1` held at some `Re s ≠ 1`, or if the
four fixed-point charts disagreed. Hits: **zero**.

---

## (C) WELD ↔ ROOT NUMBER ↔ CENTRAL RANK ↔ BSD

**Finding.** The weld cancellation encodes all three data, read from **one** double-ended
kernel, agreeing with LMFDB. Verified end-to-end on ranks 0/1/2/3
(`tmp/bsd_rank_ladder.py`, exact incomplete-Gamma kernel):

| curve | r | ε (pinned ray) | jet tower `|c₀..c₃|` | first-live `c_r` | pred (√N/2π)L^(r)(1)/r! | agree | vs lit |
|---|---|---|---|---|---|---|---|
| 11a | 0 | +1 (0.000π) | **0.134** 1e-17 1.7e-2 6e-16 | 0.13399 | 0.13399 | 1.00000 | 1.0000 |
| 37a | 1 | −1 (0.500π) | 9e-18 **0.296** 4e-16 6e-2 | 0.29624 | 0.29624 | 1.00000 | 1.0000 |
| 389a | 2 | +1 (1.000π) | 4e-7 1e-15 **2.383** 5e-15 | 2.38345 | 2.38351 | 0.99998 | 1.0000 |
| 5077a | 3 | −1 (0.502π) | 8e-17 8e-5 4e-15 **19.6** | 19.6345 | 19.6397 | 0.99974 | 1.0000 |

Reading, tied to the exact kernels:

- **(i) root number ε** = the weld sign, read from the pinned line-phase ray
  (`HingeKernel.weld_pins_half_phase`). Ray `0 ↔ ε=+1`, `π/2 ↔ ε=−1`. The a_N pinning test
  independently recovers `a_N = ε` (`bsd_weld.py`: `a_37=−1`, `a_11=+1` win the spread test).
- **(ii) central rank r** = the index of the first **live** jet. Everything below is killed
  twice: PARITY by the weld (`ε=+1 ⇒ Z even ⇒ odd jets dead` /
  `ε=−1 ⇒ Z odd ⇒ even jets dead`: `HingeKernel.even_odd_jets_dead / odd_even_jets_dead`,
  the alternating `1e-15..1e-18` entries), and RANK by the arithmetic (jets below `r`). The
  `ε=−1` case forces the hinge value itself to vanish (`weld_kills_each_phasor`,
  `weld_minus_one_forces_zero`) — the forced central zero (37a `c₀ = 9e-18`); `ε=+1` doubles
  it to the value (`weld_doubles_each_phasor`, 11a `c₀ = 0.134`).
- **(iii) BSD leading datum** `L^(r)(1)/r!` = the first live jet `c_r`, matching the
  independent G-series prediction to 5 digits (agree 0.99974–1.00000) and LMFDB/Gross-Zagier
  to `lit = 1.0000`.

**Same statistic as `rank_is_dc_residue`? YES.** `BSDClocks.rank_is_dc_residue` proves that
if the readout factors as `(s−c)^r·G` (`G(c)≠0`) then `(s−c)·F′/F → r`: the order of central
vanishing IS the DC residue of the log-derivative. The "first live jet index" read from the
weld tower is exactly this `r`; `model_form_exists` guarantees every analytic readout has such
a finite `r`. The leading value `G(c)` is extracted by `leading_jet_extraction` (`= c_r`), and
`first_jet_eq_deriv` gives the `r=1` (Gross-Zagier) case as literally a derivative.

**Tie to Sha-hinge / jet-census.** `jet_census.py test` passes all anchor gates
(E₁ kernel 6e-17, `L′(37a1,1)=0.30599977` err 3e-11, height `ĥ=0.05111141` err 5e-11,
Reg(389a1) err 8e-7) — the same `c_r` leading datum feeds
`|Sha| = [L^(r)(1)/r!]·T²/(Ω·Reg·∏c_p)`, licensed by `BSDClocks.jet_measurement_sound`
(a jet within ½ identifies the integer obstruction). |Sha|=1 lands at ranks 1/2/3
(memory: jet census).

Tier: PROVEN (weld/parity/DC-residue/jet kernels) + MEASURED (the 4-curve table, agreements
≥0.99974, LMFDB match).

**Falsification register (C).** Disconfirmed if the first live jet index disagreed with the
known rank, if ε read from the ray disagreed with LMFDB, if `c_r` missed `L^(r)(1)/r!`, or if
the parity-dead jets were not machine-zero. Hits: **zero**. (Honest caveat, from the script:
the fiber-side single-strand jet develops a ~1e-2 hinge floor by N~5000, and the a_N pinning
is masked at 5077a — but the exact double-ended kernel is clean at every rank.)

---

## (D) IS THE CROSSING SPACING PROVABLE?

**Measured law** (`tmp/oscillator.py`): first crossing at accumulated fiber-phase
**π/2** (quarter cycle), every subsequent crossing at **π** (half cycle):
ζ 0.500/1.000, χ₃ 0.499/1.000, χ₄ 0.499/1.000, χ₈ 0.499/1.000 (first/median-cell, in units of π).

**Reduction to proven kernels (this is the answer: the STRUCTURE is provable).**

- **π/2 to the FIRST crossing** ⇐ the hinge is a **turning point**. `Z(t)=Λ(½+it)` is EVEN
  (functional equation, `HingeKernel.collapseWave_even`), so `Z′(0)=0`
  (`HingeKernel.hinge_turning_point`). An even oscillator starting at a nonzero extremum
  (`Z(0)≠0`) reaches its first sign change a quarter cycle later. Verified numerically
  (`tmp/crossing_spacing.py`): `Z(0)=−3.9770`, `Z′(0)=0.0`, `Z″(0)=32.00`, even-check
  `|Z(0.7)−Z(−0.7)|=0`. For elliptic `ε=−1`, `Z` is ODD, `Z(0)=0`
  (`weld_minus_one_forces_zero`) — the hinge **is** the first crossing, offset 0, consistent.
- **π between SUBSEQUENT crossings** ⇐ the argument principle on a **real** function. In the
  exact Γ-gauge the completed fiber is REAL (`StOscillation.exact_gauge_makes_fiber_real`), so
  its phase is quantized to `{0,π}` (`StOscillation.real_arg_quantized`,
  `zeta_line_phase_quantized`); each **simple** zero forces a sign change
  (`SignChange.vanishing_forces_sign_change`), i.e. one `0↔π` toggle = Δarg π. Verified
  numerically: `N(T) = θ(T)/π + 1` (Riemann–von Mangoldt) matches the actual sign-flip count
  to `<1` zero at `T=15..41`. Each zero carries exactly π of phase — the "cell = π" law **is**
  the argument principle on the real Hardy-type fiber.

**Clean named statement (the target).** "For the exactly-gauged real fiber `Z(t)` with a
strictly-monotone accumulated phase `θ(t)` (`θ(0)=0`, extremum when `ε=+1`), the crossings are
at `θ = π/2 + kπ` (`ε=+1`) / `θ = kπ` (`ε=−1`)." The two structural pieces (`θ(0)`-offset from
evenness/oddness; `Δθ = π` per simple zero from reality + sign-change) are PROVEN. What is
**not** proven — the RH-adjacent residual — is **spacing rigidity**: that `θ` is strictly
monotone with only simple zeros, so the advance between consecutive crossings is exactly π (not
3π, 5π, …). That is the Montgomery pair-correlation regime.

Tier: PROVEN (offset structure + step structure, via the five named kernels) + MEASURED
(0.499–0.500π first, 0.999–1.000π cells; `N(T)=θ(T)/π+1`) + HYPOTHESIS/OPEN (rigidity).

**Falsification register (D).** Disconfirmed by any cell `≠ π` in the exact gauge, a first
offset `≠ π/2` (`ε=+1`) or `≠ 0` (`ε=−1`), or `N(T) ≠ θ(T)/π + 1`. Current hits: **zero**.
(The `χ₅` cell-std 0.433 is envelope-minimum mislocation near a near-double, not a cell ≠ π —
the median stays 0.999; flagged, not a hit.)

---

### One-line summary per question

- **A** clip = fiber phasor-count, **√N-scaled exactly** (exponent 0.5000, `n_eff/√N` flat to
  5 digits); arclength `√N·½lnN`. MEASURED + PROVEN window.
- **B** the weld is the **central point** `s=1`(arith)`=½`(analytic)`=t=0`, **not** the spiral
  origin — Sam's instinct confirmed. PROVEN (5 theorems) + MEASURED (balance ratio ≡1 on Re s=1).
- **C** the weld encodes ε (ray), rank r (first live jet = DC-residue), and `L^(r)(1)/r!`
  (the jet value) — all from one kernel, agreeing with LMFDB to ≥0.99974; same statistic as
  `rank_is_dc_residue`. PROVEN kernels + MEASURED ranks 0–3.
- **D** the crossing **structure** (offset π/2, step π) is PROVEN-reducible (turning point +
  argument principle on the real fiber); the spacing **rigidity** is the isolated open,
  RH-adjacent piece. MEASURED + PROVEN structure + HYPOTHESIS rigidity.
