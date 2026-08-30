# C3 proof batch 8 — 2026-08-25

Working dir `/Users/samuellavery/work/helix_frobenius`. All new artifacts under `tmp/c3b8_*`.
No tracked file edited, nothing deleted, no commits.

**My Lean compiler is permission-gated in this session.** Every `.lean` below is a
**candidate**: written, no `sorry`/`admit`/new axiom/`implemented_by`, but **not compiled by
me**. OpenAI adjudication requested (§7).

Carried in as COMPILED (adjudicated after batch 7): `tmp/c3b7_B1.lean`, `B2`, `B3`, exit 0,
all printed footprints exactly `[propext, Classical.choice, Quot.sound]`. Certified result:
`C3B7.cellDensity_pos_uncond : 20*(|x|+1)^2 ≤ modeA 0 0 u → 0 < cellDensity x u`.
The batch-6 common-δ candidate is FALSE (`x=0`, `A₁=8`, tail/head `= 1.22649971983`) and is
not reused anywhere.

---

## 1. Chart dictionary (preserved verbatim)
Native helix `Re s > 0`, phasors enter at `Re s = 0`. Xi chart `z = i(s−1/2)`:
`Re z = −Im s` (ordinate), `Im z = Re s − 1/2` (depth). `E`/`E*` = conjugate double
helix / anti-helix; chart conjugation is the FE reflection `s ↦ 1 − conj s`. Carrier chart:
physical height `Z`, analytic ordinate `t = log Z`. Native harmonization `π/3`:
`N_{π/3}(e^t)`; unit-1 **scalar receiver** `R_1(e^t) = 1 + θ(t)/π`.
`S(t) = N_{π/3}(e^t) − R_1(e^t)`, **distinct** from the Xi-chart `z` and from the Hermitian
pencil `S_t`. Distinct-event / multiplicity / classical-strip ledgers stay typed separately.

---

## 2. FAILED — with counterexamples

### 2.1 `cellDensity x u ≥ 0` on the finite window — **REFUTED**
The window is `u ∈ [0, u₁(x)]`, `2πe^{2u₁} = 20(|x|+1)²`. Computed from the batch-6 compiled
exact mode representation (`C3B6.Theta.C_tsum`), mpmath `dps = 50`, `k`-sum truncated with a
certified remainder from `|F(A,x)| ≤ 2(A+3)²e^{−A}` and `d(k) ≤ k`
(`tmp/c3b8_window.py` → `tmp/c3b8_window_out.txt`):

| x | window top `u₁` | `Cred(0,x)` | sign changes on window | at `u` |
|---|---|---|---|---|
| 0 | 0.578927603572 | +8.09940801493e−3 | 0 | — |
| 1 | 1.27207478413 | +7.71045190462e−3 | 0 | — |
| 10 | 2.97682287637 | +2.03589337764e−5 | 0 | — |
| **14.134725** | 3.29591937608 | **−2.64799904309e−7** | **1** | 0.2747 |
| **21.022** | 3.67096955726 | **−1.19209637954e−11** | **1** | 0.5504 |
| 60 | 4.68937752813 | — | **2** | 0.5862, 0.9770 |
| **88** | 5.06756397330 | +7.48700087094e−55 | **4** | 0.4223, 0.8446, 1.2669, 1.4780 |

Truncation remainders are 100+ orders below every printed digit (e.g. at `x=88, u=0`:
`rem ≤ 1.18e−153` against `Cred = 7.49e−55`).

**Consequence, stated as a property of the instrument:** no pointwise-positivity argument —
of any kind — can cover the window, because the quantity is not pointwise positive there.
`cellDensity x 0 < 0` already at the first zero ordinate `x = 14.134725`. Any window
argument must be **cumulative** (compensating), i.e. must act on `U_x(s)`, not on `C(u,x)`.
This kills, in advance, the "extend `cellDensity_pos_uncond` downward" route.

### 2.1b The cumulative leaf SURVIVES — no counterexample
Same exact mode representation, fixed-grid Simpson on a precomputed `Cred` grid, `dps = 30`
(`tmp/c3b8_utail.py` → `tmp/c3b8_utail_out.txt`).  `Ured(s,x) = ∫_s^{umax}(u−s)²e^{5u}Cred`,
sign of `Ured` = sign of `U_x(s)`:

| x | negative `Cred` grid points | `Ured(0,x)` | `Ured` at `s = u₁(x)` | verdict |
|---|---|---|---|---|
| 0 | 0 / 81 | +3.61584617857e−5 | +1.3765259364e−10 | POS |
| 1 | 0 / 81 | +3.46920289485e−5 | +2.73141949191e−34 | POS |
| 10 | 0 / 81 | +4.84878279893e−7 | +4.66362499857e−1001 | POS |
| **14.134725** | **5 / 81** | +6.05366333622e−9 | +2.31009891472e−1897 | POS |
| **21.022** | **9 / 81** | +9.97612657665e−13 | +5.43741747046e−4028 | POS |
| **60** | **10 / 81** | +2.22858395109e−37 | +1.25375711369e−31104 | POS |

**0 negative instances out of 30 tested `(x,s)` pairs.** At `x = 14.134725, 21.022, 60` the
integrand is negative on a substantial part of the grid and the cumulative integral is still
positive: the ramp compensation is doing real work, not restating pointwise positivity.
So `hramp` survives falsification and is the right leaf to attack. (Numerics falsify only;
this is not a proof.)

### 2.2 Carried FAILED (not retried)
* `C3B6.Theta.modeBound`-based `modeBound_tail_lt_head` — false at `x=0`, `A₁=8`.
* Uniform linear ramp `T(r,x) ≥ 0` — `T(0,60) = −2.4411414711711282366e−36`; this is why
  `RequestProject/WeightedTailSinhBridge.sinh_pairing_nonneg` (whose `hT` is the *linear*
  tail) is unusable and the batch-4 **quadratic** bridge must be used instead.
* Multiplicative Hankel / total positivity — `C3B7.exp_hankel_minor_neg`.

---

## 3. CANDIDATE (written, not compiled by me)

### `tmp/c3b8_A1.lean` — TARGET A: genuine `IntegrableOn` for the weighted ramp
| theorem | statement |
|---|---|
| `modeA_head_mono` | `s ≤ u → modeA 0 0 s ≤ modeA 0 0 u` |
| `modeA_head_ratio` | `modeA 0 0 u = modeA 0 0 s * exp (2(u−s))` |
| `modeA_head_lin` | `20 ≤ A₁(s) → s ≤ u → A₁(s) + 40(u−s) ≤ A₁(u)` |
| **`cellDensity_stronglyMeasurable`** | `StronglyMeasurable (cellDensity x)` — via repo's `riemannXiKernel_measurable` + `MeasureTheory.StronglyMeasurable.integral_prod_right'` |
| `cellDensity_abs_le_simple` | `20 ≤ A₁ → \|C\| ≤ 2080π²e^{5u}(A₁+3)²e^{−A₁}` |
| **`cellDensity_decay`** | `20 ≤ A₁(s) → s ≤ u → \|C(u,x)\| ≤ 33280π⁴e^{9s}e^{−A₁(s)}·e^{−31(u−s)}` |
| `sq_le_two_exp` | `0 ≤ w → w²/2 ≤ exp w` |
| **`cellDensity_ramp_integrableOn`** | `20 ≤ modeA 0 0 s → IntegrableOn (fun u => (u−s)²/2 * cellDensity x u) (Ioi s)` |
| `UTail_nonneg_analytic` | `(∀ u ∈ Ioi s, 20(\|x\|+1)² ≤ modeA 0 0 u) → 0 ≤ UTail x s` |

This closes batch-7 ledger §0.3: on the certified range `UTail` is the analytic `U_x(s)`,
not the Bochner default `0`.

### `tmp/c3b8_A2.lean` — threshold lowered `20 → 6`, i.e. to the whole half-line
Inspecting the batch-7 proofs, the *bound* half of the chain uses only `2 ≤ A₁` and
`qFac A₁ ≤ 1/4`. Restated with exactly those hypotheses, then instantiated at `A₁ ≥ 6`,
which `Real.pi_gt_three` makes automatic for every `u ≥ 0` (`2πe^{2u} ≥ 2π > 6`).

| theorem | statement |
|---|---|
| **`radial_abs_le_sharp6`** | `6 ≤ A → \|radial A (kix 0 x A) (kix 1 x A)\| ≤ 2(A+3)²e^{−A}` |
| `modeTerm_abs_le_sharp6` | `6 ≤ modeA 0 0 u → \|modeTerm x u z\| ≤ modeBndS x u z` |
| `qFac_le_quarter6` | `6 ≤ A₁ → qFac A₁ ≤ 1/4` (from `e⁴ ≥ 5 ≥ 4`) |
| `summable_gq'`, `tsum_gq'`, `tsum_gq_sq_sub'`, `modeBndS_le_prod'`, `modeBndS_le_prod_all'`, `summable_modeBndS'`, `modeBndS_tail_le'` | the batch-7 chain, hypothesis-generic |
| `modeA_head_ge_six` | `0 ≤ u → 6 ≤ modeA 0 0 u` |
| **`cellDensity_abs_le6`** | the decay bound on the **whole** half-line `u ≥ 0` |
| **`cellDensity_abs_le_simple6`** | `0 ≤ u → \|C(u,x)\| ≤ 33280π⁴e^{9u}e^{−A₁(u)}` |

The governing cubic `A³+2A²−27A−84` is `+42` at `A=6` and `−5.6` at `A=5.5`, so `6` is
essentially sharp for this packaging.

### `tmp/c3b8_A3.lean` — TARGET C: the `WeightedTail` connection
Target interface is `CriticalLinePhasor.C3B4B.sinh_pairing_nonneg_of_quadratic_ramp`
(`tmp/c3b4_A4.lean:129`); the `RequestProject` `sinh_pairing_nonneg` is unusable (its `hT`
is the refuted linear tail).

| theorem | statement |
|---|---|
| `sinh_le_half_exp`, `self_le_exp` | envelopes |
| `modeA_head_quad_lower` | `0 ≤ u → 2π(1+2u+2u²) ≤ modeA 0 0 u` |
| `gY_abs_cellDensity_le` | `gY y u·\|C(u,x)\| ≤ K·exp((2y+10)u − 4πu²)` on `u ≥ 0` |
| **`cellDensity_measurable`** | `Measurable (cellDensity x)` — bridge input `hW` ✔ |
| **`gY_abs_cellDensity_integrableOn`** | `0 ≤ y → IntegrableOn (fun u => gY y u * \|cellDensity x u\|) (Ioi 0)` — bridge input `hint` ✔ |
| **`sinh_pairing_from_cellDensity`** | the composition, with `hprodG`, `hTint`, `hqTint`, `hprodH`, `hramp` named |

Two of the seven bridge inputs are now theorems; `hramp` is the leaf.

---

## 4. ATTACK LEDGER — 26 concrete attacks

| # | attack | outcome |
|---|---|---|
| 1 | Search Mathlib for parametric-integral measurability | `StronglyMeasurable.integral_prod_right'` found (`Prod.lean:77`) |
| 2 | Search repo for `riemannXiKernel` measurability | `riemannXiKernel_measurable` found (`ThetaWronskianSuzukiGram.lean:3070`) — no `tsum`-measurability needed |
| 3 | Measurability of `cellDensity x ·` via joint measurability | constructed (A1) |
| 4 | ALT route: measurability via `continuous_tsum` + locally uniform majorant | **abandoned** — needs a `u`-uniform summable bound per window; attack 3 is strictly cheaper |
| 5 | `|C| ≤ 2080π²e^{5u}(A₁+3)²e^{−A₁}` from `cellDensity_abs_le` | constructed (A1) |
| 6 | `(A₁+3)² ≤ 4A₁²`, `A₁² = 4π²e^{4u}` → `33280π⁴e^{9u}e^{−A₁}` | constructed (A1) |
| 7 | Transport `u → s`: `A₁(u) ≥ A₁(s) + 40(u−s)` from `1+y ≤ e^y` | constructed (A1) |
| 8 | Ramp weight absorbed: `(u−s)²/2 ≤ e^{u−s}` → net `e^{−30(u−s)}` | constructed (A1) |
| 9 | `IntegrableOn` by comparison with `exp_neg_integrableOn_Ioi` | constructed (A1) |
| 10 | ALT route: `∫_0^∞ w²e^{−cw}` closed form instead of the `w² ≤ 2e^w` trick | **abandoned** — no direct Mathlib lemma; attack 8 avoids it entirely |
| 11 | Hostile window scan, 7 x-values × 25 heights, certified truncation | **B1 REFUTED**: sign changes at x ≥ 14.13 (§2.1) |
| 12 | Locate onset of sign change in `x` | between `x=10` (0 changes) and `x=14.134725` (1 change); consistent with batch-4's `u₀(x)=½log(x/2π)` |
| 13 | `cellDensity x 0` sign at the first zero ordinate | **negative**: `−2.648e−7` at `x=14.134725` |
| 14 | Threshold audit: which batch-7 steps actually need `A₁ ≥ 20` | only `qFac ≤ 1/4` and `A₁ ≥ 2`; refactor to hypothesis-generic (A2) |
| 15 | Sharpen `radial_abs_le_sharp` from `A ≥ 8` to `A ≥ 6` | constructed (A2); `6` essentially sharp (cubic `< 0` at 5.5) |
| 16 | `6 ≤ 2π` from `Real.pi_gt_three` → half-line coverage | constructed (A2) |
| 17 | Half-line decay bound `cellDensity_abs_le6` | constructed (A2) |
| 18 | Read the batch-4 bridge signatures; reject the linear-tail variant | `sinh_pairing_nonneg` unusable (refuted `hT`); use `sinh_pairing_nonneg_of_quadratic_ramp` |
| 19 | `sinh` envelope `gY y u ≤ e^u e^{2yu}/2` | constructed (A3) |
| 20 | Gaussian floor `A₁(u) ≥ 2π(1+2u+2u²)` → damping `e^{−4πu²}` | constructed (A3); works for **every** `y`, unlike the linear floor `A₁ ≥ 6+12u` which only works for `y < 1` |
| 21 | ALT route: linear floor `A₁(u) ≥ 2π(1+2u)` | **rejected** — gives `e^{(2y−2)u}`, divergent for `y ≥ 1`; attack 20 is uniform in `y` |
| 22 | `Ioi 0` integrability of the `sinh` pairing via `integrable_exp_lin_quad` | constructed (A3) |

| 23 | Cumulative-leaf sign test, 6 x-values × 5 base points, fixed-grid Simpson | **`U_x(s) ≥ 0` SURVIVES**: 0 counterexamples in 30 pairs (§2.1b) |
| 24 | Adaptive-quadrature version of attack 23 | **abandoned as too slow** — nested Bessel `k`-sums inside `mpmath.quad`; replaced by the precomputed-grid Simpson of attack 23. Recorded because the discarded run is not evidence |
| 25 | Compensation check: is positivity of `U_x` merely inherited from pointwise positivity? | **No** — at `x = 14.134725, 21.022, 60` respectively 5, 9, 10 of 81 grid points have `Cred < 0` while `Ured > 0` throughout. The ramp weight genuinely compensates |
| 26 | Split the leaf at the certified height into `Ioc s w` + `Ioi w` | designed; §8 literal next statement |

---

## 5. OPEN — smallest leaf
**`hramp : ∀ s ≥ 0, 0 ≤ ∫ u in Ioi s, (u−s)²/2 · cellDensity x u`.**

Above `20(|x|+1)² ≤ A₁(s)` this is `C3B8.UTail_nonneg_analytic` (integrand pointwise
positive, integrability now proved). **Below** it, §2.1 shows the integrand is genuinely
sign-indefinite, so the window must be handled by compensation — and §2.1b shows the
compensation numerically holds (0/30 counterexamples). Also open: the four tail-primitive
side conditions `hprodG`, `hTint`, `hqTint`, `hprodH` of the batch-4 bridge.

**Reduced form of the leaf** (via §8): with `w` the certified height, `hramp` is equivalent
to nonnegativity of the *compact* integral `∫_{Ioc s w} (u−s)²/2 · C(u,x) du` plus the
already-positive `Ioi w` part — i.e. one integral over a bounded interval, with an
integrand of both signs. That is the smallest leaf this batch produces.

## 6. EQUIV (navigation only)
`XiStructure.rh_iff_xiStructure_dominates`; `rh_iff_shallow_channel_dominates_634`;
`XiStructure.rh_of_xiStructure_isHB` (`A = ξ`); `C3B6.Theta.cellDensity_eq_tsum` (identity).

## 7. EXACT ADJUDICATION REQUEST
```
env LEAN_PATH=tmp lake env lean tmp/c3b8_A1.lean
env LEAN_PATH=tmp lake env lean tmp/c3b8_A2.lean     # imports c3b8_A1
env LEAN_PATH=tmp lake env lean tmp/c3b8_A3.lean     # imports c3b8_A2, c3b4_A4
```
(oleans for `c3b8_A1`, `c3b8_A2` needed before `A3`). Expected fragile points, in order:
`hmeas.stronglyMeasurable.integral_prod_right'` unification against the `cellDensity`
lambda; `unfold modeBndS; norm_num` producing the `(0,0)` head form; the `nlinarith` in
`cellDensity_abs_le_simple`/`_simple6`; `Real.sinh_le_sinh.mpr` for `0 ≤ sinh`; and
`cellDensity_abs_le6`'s final `linarith [hhead, hnorm, htail]` (names local to that proof).

## 8. LITERAL NEXT LEAN STATEMENT
```lean
-- tmp/c3b8_A4.lean, after `import c3b8_A3`, namespace C3B8.
-- The window must be compensated, not made pointwise positive (§2.1).
-- Split the leaf at the certified height and keep only the window integral open.
theorem UTail_split (x : ℝ) {s w : ℝ} (hsw : s ≤ w)
    (hw : 20 * (|x| + 1) ^ 2 ≤ modeA 0 0 w) :
    (∫ u in Set.Ioi s, (u - s) ^ 2 / 2 * cellDensity x u)
      = (∫ u in Set.Ioc s w, (u - s) ^ 2 / 2 * cellDensity x u)
        + ∫ u in Set.Ioi w, (u - s) ^ 2 / 2 * cellDensity x u
```
with the second summand nonnegative by `C3B7.cellDensity_pos_uncond`, so the whole leaf
reduces to a **compact** integral over `Ioc s w`. Ingredients present:
`cellDensity_ramp_integrableOn` (A1), `cellDensity_measurable` (A3),
`Set.Ioc_union_Ioi_eq_Ioi`, `MeasureTheory.setIntegral_union`.

---

## 9. Artifacts
| file | what |
|---|---|
| `tmp/c3b8_A1.lean` | TARGET A — measurability + decay + `IntegrableOn` (candidate) |
| `tmp/c3b8_A2.lean` | threshold `20 → 6`, half-line decay bound (candidate) |
| `tmp/c3b8_A3.lean` | TARGET C — `WeightedTail` connection, 2 of 7 inputs discharged (candidate) |
| `tmp/c3b8_window.py` / `_out.txt` | **B1 refutation**: window sign changes, certified truncation |
| `tmp/c3b8_utail.py` / `_out.txt` | cumulative-leaf sign test (running) |

No claim about RH or GRH is made anywhere in this batch.
