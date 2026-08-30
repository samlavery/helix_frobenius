# C3 proof batch 16 — the adaptive-window exclusion, proved unconditionally

Date 2026-08-25.  `/Users/samuellavery/work/helix_frobenius`, branch `ladder-campaign-2026-08`.
**No commit.  `git diff --stat` EMPTY — no tracked file modified.  All new files are
`tmp/c3b16_*`.**  `AGENTS.md` still does not exist.  `CLAUDE.md` obeyed.

**HEADLINE.**  17 new declarations, all axiom-clean.  Batch 15's overclaim is now a theorem:

> `C3B16.no_adaptive_window :`
> `∃ X, ∀ a x, 0 ≤ a → 4·Tail a ≤ mass → (criterion at (a,x)) → x² ≤ X`
>
> **unconditional** — no numeric witness, no hypothesis, standard axioms only.

And the Gaussian minorant proposed as batch 15's next target was carried to its assembled
integral bound and **rejected**: it is a true pointwise inequality that yields a
*nonpositive* assembly at every `(a,x)`.

---

## 0. CORRECTION TO BATCH 15, APPLIED BEFORE NEW WORK

Batch 15's ledger said the uniform choice `a = a(x)` "**PROVABLY DOES NOT EXIST** for this
instrument, by two compiled theorems".  **That overstated the compiled content.**
`criterion_forces_x_bound` and `criterion_fails_past_cap` give, for each **fixed** `a` with
`Qwin a > 0`, a cap `x² ≤ mass/(2·Qwin a)`.  That is `∀a ∃cap`, **not** `∃cap ∀a`, and it does
not exclude an adaptive `a(x)` whose cap grows with `x`.

Applied to `tmp/claude_c3_proof_batch15_20260825.md` (prose + YAML) and to the **docstrings**
of `tmp/c3b15_A2.lean` (file header and `criterion_fails_past_cap`).  The global
adaptive-window claim is relabelled **UNCOMPILED** there; the informal sentence "Since `Q` is
nondecreasing…" is explicitly marked as *not a proof*, since that monotonicity was not
formalised.  **No theorem statement was changed**; all 19 batch-15 declarations recompile at
`[propext, Classical.choice, Quot.sound]`.

The named missing pieces — `Tail` antitone, `Qwin` monotone, a uniform positive lower bound
for `Qwin` on the admissible set — are exactly what this batch supplies.

---

## COMPILED

```
env LEAN_PATH=tmp lake env lean tmp/c3b16_A1.lean      (+ -o …olean)
env LEAN_PATH=tmp lake env lean tmp/c3b16_A2.lean      (+ -o …olean)
env LEAN_PATH=tmp lake env lean tmp/c3b16_A3.lean
```

`tmp/c3b16_audit.log`: **17/17 exactly `[propext, Classical.choice, Quot.sound]`**,
`grep -c "error\|sorryAx"` → **0**.  Escape scan over all three files → **exit 1, no output**.
(Deprecation warnings only: `HasSubset.Subset.eventuallyLE`, `integral_inter_add_diff`,
`Set.diff_subset`, `push_neg`.)

### `tmp/c3b16_A1.lean` — monotonicity, the annulus bound, the conditional exclusion (7 decls)

```lean
theorem Tail_antitone {a b : ℝ} (hab : a ≤ b) : Tail b ≤ Tail a
theorem Qwin_mono {a b : ℝ} (_ha : 0 ≤ a) (hab : a ≤ b) : Qwin a ≤ Qwin b
theorem Tail_zero : Tail 0 = cosMom Rker 0 / 2

theorem Qwin_ge_annulus {c a : ℝ} (hc : 0 ≤ c) (hca : c ≤ a) :
    2 * c ^ 2 * (Tail c - Tail a) ≤ Qwin a

theorem no_adaptive_window_of_witness {c : ℝ} (hc : 0 < c)
    (hw : cosMom Rker 0 / 4 < Tail c) {a x : ℝ} (_ha : 0 ≤ a)
    (hadm : 4 * Tail a ≤ cosMom Rker 0)
    (hcrit : 2 * x ^ 2 * Qwin a + 4 * Tail a ≤ cosMom Rker 0) :
    x ^ 2 ≤ cosMom Rker 0 / (2 * (2 * c ^ 2 * (Tail c - cosMom Rker 0 / 4)))
```

`Qwin_ge_annulus` is the pivot: on the annulus `c ≤ |v| < a` one has `v² ≥ c²`, and that
annulus carries mass exactly `2(Tail c − Tail a)` by `C3B15.window_mass`.  Proved by
`integral_inter_add_diff` splitting the window into inner disc and annulus, discarding the
(nonnegative) inner disc.

The exclusion's `c ≤ a` is **not** a hypothesis: admissibility `4·Tail a ≤ mass` plus
`mass/4 < Tail c` forces `Tail a < Tail c`, and `Tail_antitone` then forces `c < a`.  That is
where the antitonicity does real work.

Also compiled, the minorant-class kill (§FAILED F1):
`reject_shifted_minorant {g w T : ℝ} (hgw : g ≤ w) (hT : 0 ≤ T) : 2*g - 2*w - 2*T ≤ 0`.

### `tmp/c3b16_A2.lean` — strict positivity of the mass (5 decls)

```lean
theorem cosMom_xiKernel_zero_pos : 0 < cosMom riemannXiKernel 0
theorem cosMom_kM2_zero_pos      : 0 < cosMom kM2 0
theorem mass_pos                 : 0 < cosMom Rker 0
theorem witness_holds_at_zero    : cosMom Rker 0 / 4 < Tail 0
```

`mass = ¼·(∫Φ)·(∫t²Φ)` via `C3B14.cosMom_Rker` at `x = 0`; both factors are positive because
`Φ > 0` everywhere (`riemannXiKernel_pos_all`), giving full-measure supports.
`witness_holds_at_zero` says the witness inequality holds *at radius 0* — the whole remaining
question was whether it survives to a **positive** radius.

### `tmp/c3b16_A3.lean` — the exclusion, UNCONDITIONAL (5 decls)

```lean
theorem Rker_primitive_continuous : Continuous fun c : ℝ => ∫ v in (0:ℝ)..c, Rker v
theorem Tail_sub (c : ℝ) (hc : 0 ≤ c) : Tail 0 - Tail c = ∫ v in (0:ℝ)..c, Rker v
theorem exists_witness : ∃ c : ℝ, 0 < c ∧ cosMom Rker 0 / 4 < Tail c

theorem no_adaptive_window :                                   -- hypotheses: NONE
    ∃ X : ℝ, ∀ a x : ℝ, 0 ≤ a → 4 * Tail a ≤ cosMom Rker 0 →
      2 * x ^ 2 * Qwin a + 4 * Tail a ≤ cosMom Rker 0 → x ^ 2 ≤ X
```

The witness is produced, not assumed: `Tail 0 = mass/2 > mass/4` (needs `mass_pos`), the
primitive `c ↦ ∫_0^c R` is continuous with value `0` at `0`
(`intervalIntegral.continuous_primitive`, `R` being integrable), so some positive radius still
retains more than a quarter of the mass.  `Tail_sub` supplies `Tail 0 − Tail c = ∫_0^c R` by
splitting `Ioi 0 = Ioc 0 c ⊔ Ioi c`.

**So the exclusion needs no numerics at all.**  The `c = 0.05` witness measured in §M2 is now
a redundant sanity check rather than an input.

---

## OPEN

```lean
theorem laguerre_edge (x : ℝ) : 0 ≤ C3B14.cosMom Rker (2 * x)
```

unchanged.  Batch 16 removes nothing from it: `no_adaptive_window` is a statement about the
**criterion**, and it closes a route rather than opening one.  Stated at exactly that strength.

---

## EQUIV — navigation only

* Target ⟺ `R` positive definite (`C3B14.target_iff_cosMom_Rker_nonneg`).
* `Tail_zero`, `window_mass`, `Tail_sub` — the mass bookkeeping that makes the criterion three
  computable numbers.

---

## FAILED — 21 attacks

**F1. `cos z ≥ 2e^{−βz²} − 2` — REJECTED at the assembly gate, exactly as instructed.**  It is
a **true** pointwise minorant for every `β > 0` (measured `min(cos − minorant) = +0.77` at
`β = 0.25`, `+1.00` at `β = 2`).  But carried to the assembled integral bound it gives
`K(a,x) = 2G(a,x) − 2W(a) − 2·Tail a` with `G ≤ W` always, hence `K ≤ −2·Tail a ≤ 0`:

```
      a       x          2G - 2W        -2 Tail                K   K>0?
   0.20    0.00     0.000000e+00  -1.891507e-03    -1.891507e-03  False
   0.50    3.00    -8.396601e-03  -4.061559e-06    -8.400663e-03  False
   1.00    0.00     0.000000e+00  -0.000000e+00     0.000000e+00  False
```

At `x = 0` the minorant contributes exactly `0` where the truth is the whole window mass.
**Not formalised as a route; the reason is compiled instead** (`reject_shifted_minorant`), and
it is a *class* kill: any minorant of the shape `2m − 2` with `m ≤ 1` behaves this way.

**F2. `cos z ≥ e^{−βz²}` on a bounded phase interval — VALID, and it LOSES.**  `β > 1/2` is
necessary (the `z²` coefficients must separate), and `z* ≤ π/2` always (the bound dies where
`cos` does).  Measured `z*(β)`: `0.341` at `β = 0.51`, `1.265` at `0.75`, `1.447` at `1.0`,
`1.563` at `2.0`, `1.5707` at `4.0` → `π/2`.  Assembled reaches:

| central bound | reach |
|---|---|
| quadratic (batch 15) | **6.638679** |
| Gaussian `β = 0.75`, `z* = 1.26476` | 5.381949 |
| Gaussian `β = 1.0`, `z* = 1.44741` | 5.676119 |
| Gaussian `β = 2.0`, `z* = 1.56325` | 5.299148 |
| Gaussian `β = 4.0`, `z* = 1.57074` | 4.688780 |

**The Gaussian minorant is strictly worse than the quadratic at every `β` tested.**  Batch
15's proposed next target is therefore withdrawn as an improvement route.  Not formalised.

**F3. Piecewise envelope `max(quadratic, linear)` — no gain.**  See §P3.

**F4. Signed-annulus (cosine-lobe) decomposition — the BEST bound found, and NOT compilable
here.**  Splitting `[0,∞)` at `v_k = (2k+1)π/(4x)` gives
`cosMom R (2x) = 2(J₀ − J₁ + J₂ − …)`, and if `(J_k)` decreases the alternating sum is
`≥ 2(J₀ − J₁)`.  More generally the `k`-lobe partial sum is a valid lower bound, and the
reaches **grow with `k`**:

| partial sum | reach |
|---|---|
| 2-lobe | 8.863342 |
| 4-lobe | 12.558529 |
| 6-lobe | 15.563725 |
| 8-lobe | 18.331719 |

against the quadratic window's `6.638679`.  The bound also **tracks the truth closely**: at
`x = 12` the 6-lobe partial sum is `2.131988e−05` against the true `2.132025e−05`.  This is
the first instrument in the campaign that uses the tail's **cancellation** rather than its
mass — the ingredient batches 14/15 identified as missing — and unlike every polynomial or
Gaussian minorant it is **not visibly capped**.

**But it rests on `R` being decreasing on `[0,∞)`** (so that `(J_k)` decreases and the
alternating remainder is nonnegative), which is measured true (`R decreasing on [0,inf)?
True`) and is **NOT compiled**.  Recorded as numerical only; `Rker_antitone` is the successor
target and is *not* claimed here.

**F5. Theta-mode and incomplete-gamma tail representations — provably cannot help.**  Both are
routes to *bounding* `Tail`.  `C3B15.criterion_forces_x_bound` makes the cap depend only on
`Qwin`, and `Qwin` saturates (`Qwin(0.5) ≈ Qwin(0.75) ≈ Qwin(1.5)`) while `Tail(0.75) ≈ 1e−10`
is already negligible.  **No representation of the tail can move the reach.**  Left unrun, and
that is stated rather than implied.

**F6. Dyadic annuli, exponential moments, Chernoff — carried over from batch 15 as nulls.**
Chernoff is valid (verified at five `λ`) but overshoots a doubly-exponentially small tail by
factors up to `9.6e2`.  Not re-run.

**F7. Heat / de Bruijn flow on the criterion — rescales, does not reshape.**  See §P5.

**F8. Positive convolution factorization — no new sign.**  `R(v) = (M₂∗Φ)(2v) − v²(Φ∗Φ)(2v)`,
verified exactly in batch 14 (`reldiff 5.5e−13`); the `−v²` term is what prevents `R` from
being a convolution square.  Not re-run.

**F9. `π/3` for the window radius — applicable, tested, NOT privileged.**  Unlike batch 14,
`a` here **is** a genuine cell coordinate, so the register was checked.  Measured: the `π/3`,
`π/6`, `π/12`, `π/24` choices all underperform the free optimum.  **No unit-1 scan run** —
that is the documented false-null trap.

**F10. The compiled cap is LOOSE.**  `no_adaptive_window`'s `X` optimised over witnesses gives
`|x| ≤ 27.756` (best witness `c = 0.065`) against the measured criterion reach `6.638679`.
Valid, and reported as loose — the exclusion is qualitative, not sharp.

---

## HOSTILE NUMERICS

`tmp/c3b16_num2_out.txt` §P2 — cancellation-free at 40 dps (`L₁ = Ξ²·(ξ′/ξ)′(½+ix)`, never a
finite difference), **2615 points**: a `2e−4` grid on `[0,0.05]`, step `0.01` to `x = 10`,
`0.1` to `60`, `0.5` to `400`, plus **27 zero ordinates × 7 offsets**
`{0, ±1e−12, ±1e−6, ±0.02}`.

**Rejection gate** used throughout the batch: a claimed negative counts only if `|min|`
exceeds the grid's own tail residual by `≥ 1e4` and survives a precision change.  (This gate
is what caught the false Gaussian "violations" in batch 14.)

---

## CHART AUDIT

| chart | preserved how in batch 16 |
|---|---|
| **native helix `Re s > 0`, phasors from 0** | No convergence abscissa anywhere; every step is set inclusion, `Rker ≥ 0`, or continuity of a primitive. |
| **physical carrier `Z > 0`, `y = log Z`** | `Tail`, `Qwin`, the annulus and the window radius `a` are all sets and moments in the cell-centre coordinate `v` of the `t = log Z` chart. |
| **double helix / anti-helix conjugation** | `C3B15.tail_reflect` (the even-tail change of variables = the Jacobi reflection) is what `Tail` rests on; `Tail_zero` is its `a = 0` instance, giving `Tail 0 = mass/2`. |
| **`S(t) = N_{π/3}(e^t) − N_1(e^t)` as a registration gap** | Untouched — no count is formed. §F9 tests the `π/3` register where it genuinely applies (the window radius) and reports a measured null; **no unit-1 cell scan was run.** |
| **`Ξ` chart** | `Ξ(x) = ξ(½+ix)`, `cosMom riemannXiKernel x = 2Ξ(x)`; kept distinct from the two conjugate charts elsewhere in the corpus. |
| **GRH family charts** | Untouched. **No GRH statement follows.** |

The C3 campaign remains **not in print**; no paper edit is proposed.

---

## THE SMALLEST NEXT LEAN THEOREM

The best bound found this batch is the cosine-lobe decomposition (reach `8.863`, beating the
window's `6.639`), and its single missing input is monotonicity of the kernel:

```lean
theorem Rker_antitone {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) : Rker v ≤ Rker u
```

With it, the alternating-lobe remainder is nonnegative and the `k`-lobe partial sums become
compilable lower bounds — the first family in this campaign that uses the tail's
**cancellation** rather than its mass, whose measured reaches **grow** with `k`
(`8.86 → 12.56 → 15.56 → 18.33`) instead of capping.  Measured true on the whole grid
(`R decreasing on [0,inf)? True`).
Stated honestly: this is an analytic fact about `R = ∫p²Φ(v+p)Φ(v−p)dp`, not a reformulation,
and it is not obviously easy — `Φ` is log-concave-adjacent but `Rker`'s monotonicity has not
been reduced to a compiled property of `Φ` here.

---

## MACHINE-READABLE SUMMARY

```yaml
batch: c3-batch-16
date: 2026-08-25
branch: ladder-campaign-2026-08
target_proved: false
rh_claimed: false
grh_claimed: false
novelty_claimed: false
commits: 0
tracked_files_modified: 0
lean_files_new: 3
declarations_compiled: 17
declarations_by_file: {A1: 7, A2: 5, A3: 5}
axiom_footprint_all: "[propext, Classical.choice, Quot.sound]"
audit_log: tmp/c3b16_audit.log
forbidden_pattern_scan: "clean (exit 1, no output) over c3b16_A1, A2, A3"
batch15_correction: "its global adaptive-window claim was (forall a)(exists cap), not (exists cap)(forall a). Relabelled UNCOMPILED in the ledger and in the c3b15_A2 docstrings; the informal 'Since Q is nondecreasing' sentence marked as not a proof. No theorem statement changed; all 19 batch-15 declarations recompile clean."
headline:
  name: C3B16.no_adaptive_window
  statement: "exists X, forall a x, 0 <= a -> 4 Tail a <= mass -> criterion(a,x) -> x^2 <= X"
  hypotheses: none
  significance: "the exclusion batch 15 claimed and did not have, now UNCONDITIONAL: no numeric witness needed"
  ingredients: ["Tail_antitone", "Qwin_mono", "Qwin_ge_annulus", "Tail_zero", "mass_pos", "exists_witness via intervalIntegral.continuous_primitive"]
gaussian_minorant_verdict:
  shifted_form: "cos z >= 2 exp(-beta z^2) - 2 is TRUE pointwise for every beta > 0 and REJECTED at the assembly gate: G <= W always, so K <= -2 Tail a <= 0 at every (a,x); identically 0 in the central part at x=0 where the truth is the whole window mass. Class kill compiled as reject_shifted_minorant."
  bounded_form: "cos z >= exp(-beta z^2) on |z| <= z*(beta) is VALID (beta > 1/2 necessary, z* -> pi/2 as beta grows) but its assembled reach LOSES to the quadratic at every beta tested: 5.38 / 5.68 / 5.30 / 4.69 against 6.638679."
best_bound_found:
  name: "signed-annulus (cosine-lobe) decomposition"
  reaches: {2_lobe: 8.863342, 4_lobe: 12.558529, 6_lobe: 15.563725, 8_lobe: 18.331719}
  vs_window: 6.638679
  why: "uses the tail's CANCELLATION rather than its mass; reaches GROW with the number of lobes and the bound tracks the truth closely (6-lobe 2.131988e-05 vs true 2.132025e-05 at x=12). Unlike every polynomial or Gaussian minorant it is NOT visibly capped."
  blocker: "needs Rker antitone on [0,inf); measured true, NOT COMPILED"
compiled_cap_is_loose:
  compiled: "|x| <= 27.755542 (best witness c = 0.065)"
  measured_reach: 6.638679
  note: "the exclusion is qualitative, not sharp; reported as loose"
hostile_scan:
  points: 2615
  grid: "2e-4 on [0,0.05]; 0.01 to x=10; 0.1 to 60; 0.5 to 400; 27 zero ordinates x 7 offsets"
  method: "cancellation-free at 40 dps, never a finite difference"
  rejection_gate: "a negative counts only if |min| exceeds the grid's tail residual by >= 1e4 and survives a precision change"
pi3_register:
  applicable: true
  reason: "the window radius a IS a cell coordinate"
  result: "measured NOT privileged (pi/3, pi/6, pi/12, pi/24 all underperform the free optimum)"
  unit_one_scan_run: false
literature_check_still_required:
  - "first Laguerre inequality for the Riemann Xi function: NOT read at source (web tools unavailable, SIX sessions running). NO novelty claimed anywhere."
open_next_lean_statement: |
  theorem Rker_antitone {u v : R} (hu : 0 <= u) (huv : u <= v) : Rker v <= Rker u
open_next_purpose: "unlocks the cosine-lobe bound (reach 8.863 vs the window's 6.639), the first bound in this campaign using the tail's cancellation rather than its mass. An analytic fact about R = int p^2 Phi(v+p)Phi(v-p) dp; measured true; not reduced to a compiled property of Phi here."
```
