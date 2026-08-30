# C3 proof batch 15 — the window bound repaired, and the first criterion with a reach

Date 2026-08-25.  `/Users/samuellavery/work/helix_frobenius`, branch `ladder-campaign-2026-08`.
**No commit.  `git diff --stat` EMPTY — no tracked file modified.  All new files are
`tmp/c3b15_*`.**  `AGENTS.md` still does not exist.  `CLAUDE.md` obeyed.

**HEADLINE.**  19 new declarations, all axiom-clean.  Batch 14's proposed next theorem was
**false**; it is retracted, repaired, and compiled.  On top of it sits the first criterion in
this campaign with a genuine **reach**: an inequality in which *every quantity is an explicit
integral of the nonnegative kernel `R`*, satisfiable exactly for **|x| ≤ 6.6387** — against
batch 13's best conditional reach of `2.503` and batch 12's single point `x = 0`.  Coverage
on `[0,60]`: **11.07%**, up from 4.41%.

---

## 0. CORRECTION TO BATCH 14, APPLIED BEFORE NEW WORK

Batch 14's ledger proposed as its "smallest next Lean theorem":

```lean
-- FALSE:
    2 * (∫ v in Ioo (-a) a, Rker v * cos (2*x*v)) - 2 * (∫ v in Ioi a, Rker v)
      ≤ cosMom Rker (2*x)
```

**It is false, and it fails at `x = 0`.**  With `S := ∫_{(0,∞)}R` and `cosMom Rker 0 = 2S`,
as `a → ∞` the left side tends to `2·(2S) − 0 = 4S` while the right side is `2S`, so the
claim asserts `S ≤ 0`; measured, `2S = 1.14198308344e−02 > 0`.  The error is arithmetic: the
window and its complement **partition** the line, so the central piece carries coefficient
**1**.

Marked RETRACTED in `tmp/claude_c3_proof_batch14_20260825.md` (both occurrences), with the
replacement printed there.  Orientation re-tested over 30 hostile `(a,x)` pairs
(`tmp/c3b15_num1_out.txt` §W0/W1): the retracted form is violated **24** times, the corrected
form **0** times.

---

## COMPILED

Commands, literal:

```
env LEAN_PATH=tmp lake env lean tmp/c3b15_A1.lean
env LEAN_PATH=tmp lake env lean -o tmp/c3b15_A1.olean tmp/c3b15_A1.lean
env LEAN_PATH=tmp lake env lean tmp/c3b15_A2.lean
```

`tmp/c3b15_audit.log`: **19/19 exactly `[propext, Classical.choice, Quot.sound]`**,
`grep -c "error\|sorryAx"` → **0**.  Escape scan over both files → **exit 1, no output**.
(One deprecation warning: `integral_union_ae`; harmless, no axiom effect.)

### `tmp/c3b15_A1.lean` — the corrected window bound and two central bounds (10 decls)

```lean
theorem tail_reflect (a : ℝ) : (∫ v in Iic (-a), Rker v) = ∫ v in Ioi a, Rker v
theorem compl_mass (a : ℝ) (ha : 0 ≤ a) :
    (∫ v in (Ioo (-a) a)ᶜ, Rker v) = 2 * ∫ v in Ioi a, Rker v
theorem window_mass (a : ℝ) (ha : 0 ≤ a) :
    (∫ v in Ioo (-a) a, Rker v) = cosMom Rker 0 - 2 * ∫ v in Ioi a, Rker v

theorem window_lower_tail (a x : ℝ) (ha : 0 ≤ a) :          -- THE CORRECTED THEOREM
    (∫ v in Ioo (-a) a, Rker v * Real.cos (2 * x * v)) - 2 * (∫ v in Ioi a, Rker v)
      ≤ cosMom Rker (2 * x)

theorem central_ge_quadratic (a x : ℝ) :                     -- no constraint on x or a
    (∫ v in Ioo (-a) a, Rker v) - 2 * x ^ 2 * (∫ v in Ioo (-a) a, v ^ 2 * Rker v)
      ≤ ∫ v in Ioo (-a) a, Rker v * Real.cos (2 * x * v)

theorem central_ge_linear (a x : ℝ) (ha : 0 ≤ a) (hax : 2 * |x| * a ≤ Real.pi / 2) :
    (∫ v in Ioo (-a) a, Rker v) - (4 * |x| / Real.pi) * (∫ v in Ioo (-a) a, |v| * Rker v)
      ≤ ∫ v in Ioo (-a) a, Rker v * Real.cos (2 * x * v)
```

`window_lower_compl` (the complement form, needing no set algebra) is proved first;
`window_lower_tail` follows from it through `compl_mass`, whose content is the **even-tail
change of variables** `tail_reflect` — Mathlib's `integral_comp_neg_Iic` supplying the
reflection and `C3B14.Rker_even` the invariance of the integrand.  The `AEDisjoint` step is
`Iic(-a) ∩ Ici a ⊆ Icc a (-a)`, which is null for `a ≥ 0` (including `a = 0`, where it is the
single point `{0}`).

**The two central bounds are independent and genuinely complementary in sharpness.**
`central_ge_quadratic` uses Mathlib's `Real.one_sub_sq_div_two_le_cos` and is valid for
**every** `x, a`; `central_ge_linear` uses `Real.one_sub_mul_le_cos` and is valid on
`2|x|a ≤ π/2`, where it is sharper near the endpoint — at `z = π/2` it is **exact** (`0`),
where the quadratic gives `−0.2337`.  Both were pre-tested against the exact central integral
before formalisation (§C1/C2), every printed bound checked `≤` the exact column.

The bounded-window integrability facts (`sq_Rker_integrableOn`, `abs_Rker_integrableOn`) are
proved by domination: on `Ioo(-a,a)`, `v² ≤ a²` and `|v| ≤ a`, so `v²R` and `|v|R` are
dominated by constants times `R`.

### `tmp/c3b15_A2.lean` — the checkable criterion and the exact trade-off (9 decls)

```lean
def Qwin (a : ℝ) : ℝ := ∫ v in Ioo (-a) a, v ^ 2 * Rker v     -- window second moment
def Tail (a : ℝ) : ℝ := ∫ v in Ioi a, Rker v                  -- tail mass

theorem window_criterion_quadratic {a x : ℝ} (ha : 0 ≤ a)
    (h : 2 * x ^ 2 * Qwin a + 4 * Tail a ≤ cosMom Rker 0) :
    0 ≤ cosMom Rker (2 * x)

theorem window_criterion_linear {a x : ℝ} (ha : 0 ≤ a) (hax : 2 * |x| * a ≤ Real.pi / 2)
    (h : (4 * |x| / Real.pi) * Awin a + 4 * Tail a ≤ cosMom Rker 0) :
    0 ≤ cosMom Rker (2 * x)

theorem criterion_needs_small_tail {a x : ℝ} (h : …) : 4 * Tail a ≤ cosMom Rker 0
theorem criterion_forces_x_bound {a x : ℝ} (hQ : 0 < Qwin a) (h : …) :
    x ^ 2 ≤ cosMom Rker 0 / (2 * Qwin a)
theorem criterion_fails_past_cap {a x : ℝ} (hQ : 0 < Qwin a)
    (hx : cosMom Rker 0 / (2 * Qwin a) < x ^ 2) : ¬ (…)
```

**This is not a conditional restatement.**  The hypothesis mentions neither the target, nor
`Ξ`, nor any zero: it is an inequality between three explicit integrals of the nonnegative
kernel `R`, all of which are finite numbers one can compute.  `window_criterion_at_zero`
recovers `C3B14.cosMom_Rker_zero_nonneg` *through* the criterion rather than around it.

---

## THE REACH, AND THE ATTEMPTED UNIFORM `a = a(x)`

**Measured reach** (`tmp/c3b15_num3_out.txt` §H1/H2), optimising `a` for each `x`:

| instrument | reach | coverage on `[0,60]` |
|---|---|---|
| batch 12 (`momentTwo_zero_nonneg`) | the single point `x = 0` | 1/1201 |
| batch 13 (`momentTwo_nonneg_of_either`) | `\|x\| ≤ 2.503` | 53/1201 = 4.41% |
| **batch 15 `window_criterion_quadratic`** | **`\|x\| ≤ 6.638679`** | **133/1201 = 11.07%** |
| with the degree-6 Taylor central bound | `\|x\| ≤ 6.805123` | — |

The compiled implication was checked **end to end** at eleven hostile ordinates: wherever the
hypothesis holds, `L₁(x) ≥ 0` — **0 violations**.  The table also shows the hypothesis
correctly *failing* past the reach (at `x = 7, 9, 14.1347`), so the criterion is not vacuous
in either direction.

> ## ⚠ CORRECTED 2026-08-25 (OpenAI adjudication) — the global claim below is UNCOMPILED
>
> The first release of this section said the uniform choice `a = a(x)` "**PROVABLY DOES NOT
> EXIST** for this instrument, by two compiled theorems".  **That overstates what is
> compiled.**  `criterion_forces_x_bound` and `criterion_fails_past_cap` establish, for each
> **fixed** `a` with `Qwin a > 0`, a cap `x² ≤ mass/(2·Qwin a)`.  That is `∀a ∃cap`, not
> `∃cap ∀a`, and it does **not** by itself exclude an adaptive `a(x)` whose cap grows without
> bound as `x` grows.
>
> The stronger conclusion additionally needs: `Tail` **antitone**, `Qwin` **monotone** on
> `a ≥ 0`, and a **uniform positive lower bound** for `Qwin a` over the admissible set
> `{a : 4·Tail a ≤ mass}` — or some other argument.  **None of those was compiled in batch
> 15.**  The global adaptive-window exclusion is therefore relabelled **UNCOMPILED**; what
> follows is the per-`a` statement, which is compiled, plus a numerical observation.
>
> (Batch 16 supplies the missing monotonicity and an annulus lower bound, reducing the
> exclusion to a single explicit numeric fact.)

**The per-`a` cap is compiled; the global adaptive-window exclusion is NOT.**  Two compiled
theorems pin the trade-off *at fixed `a`*, and neither is an assertion about the target:

* `criterion_needs_small_tail` — the hypothesis forces `4T(a) ≤ cosMom R 0`: **the tail must
  carry at most a quarter of the mass**, a constraint on `a` alone.  So `a` cannot shrink.
* `criterion_forces_x_bound` — the hypothesis forces `x² ≤ cosMom R 0 / (2Q(a))`: for each
  admissible `a` there is a **finite `x`-cap**.

Measured together (§H4):

```
      a            Q(a)            T(a)  4T<=mass?   cap on |x|  criterion fires to
   0.10    1.823490e-05    2.796085e-03       True    17.695514            2.541092
   0.15    5.197074e-05    1.709729e-03       True    10.481788            6.638679   <- optimum
   0.30    1.845550e-04    2.076592e-04       True     5.562268            5.356160
   0.75    2.362957e-04    9.765172e-11       True     4.915718            4.915717
```

`Q(a)` saturates at `≈2.363e−4` by `a = 0.75`, so the cap tends to `√(mass/2Q(∞)) = 4.9157`;
the optimum `6.6387` at `a = 0.15` is the best trade against the tail term.

**Why the cap is a property of the INSTRUMENT.**  A polynomial minorant `cos z ≥ P(z)` has
`P(z) → −∞`, while the true central integral decays like `e^{−πx/2}`.  No polynomial tracks
exponential decay, so any polynomial-central-bound criterion caps.  **The cheapest experiment
that would refute this is a non-polynomial central minorant with a computable moment** — for
instance a Gaussian minorant `cos z ≥ αe^{−βz²} − γ` with pre-registered constants.  It was
**not** run.  Prediction, for the record: a Gaussian minorant would extend the reach but
still cap, because the *tail* term `4T(a)` is `x`-independent and the criterion must beat it
with a quantity that vanishes as `x → ∞`.

---

## OPEN

```lean
theorem laguerre_edge (x : ℝ) : 0 ≤ C3B14.cosMom Rker (2 * x)
```

unchanged.  Batch 15 removes nothing from it formally — `window_criterion_quadratic` is an
implication whose hypothesis is not proved to hold at any `x` in Lean; the reach `6.6387` is
a **numerical** evaluation of that hypothesis.  Stated at exactly that strength.

---

## EQUIV — navigation only

* **Target ⟺ `R` positive definite** (`C3B14.target_iff_cosMom_Rker_nonneg`, compiled).
* `cosMom R (2x) = 2·∫_{(0,∞)}u²C(x,u)du` (compiled bridge to batch 12's engine).
* `window_mass`: the window carries all mass but the two tails — the identity that turns the
  criterion into three computable numbers.

---

## FAILED — 21 decompositions, and three defects of my own

**F1. Dyadic annuli — null.**  `T(a) = Σ_k ∫_{2^k a}^{2^{k+1}a}R` is exact by construction
(`reldiff 0.00e+00` at four `a`), and buys nothing: `R` decays doubly exponentially, so the
first annulus already carries essentially the whole (tiny) tail.

**F2. Chernoff / exponential moments — valid but lossy.**  The claim
`∫e^{λ|v|}R dv ≤ ¼B₀(λ)B₂(λ)`, with `B_j(λ) = ∫t^j e^{λ|t|/2}Φ(t)dt` and `B₁ = 0` by parity,
was derived through `(t,s) = (v+p, v−p)`, `2|v| ≤ |t|+|s|`, `dv dp = ½dt ds`, and **verified**
at five `λ` (`LHS ≤ RHS` at every one).  But it produces an *exponential* bound for a
*doubly-exponentially* small quantity: measured overshoot `T(0.3)` by `2.4e1`, `T(0.5)` by
`1.6e2`, `T(0.75)` by `9.6e2`.  Valid, recorded, not used.

**F3. Theta-mode sums and incomplete-gamma tails — not needed, and provably so.**  These are
routes to *bounding* `T(a)`.  The compiled `criterion_forces_x_bound` shows the cap depends
only on `Q(a)`, and §H4 shows `Q` is saturated by `a = 0.75` while `T(0.75) = 9.8e−11` is
already negligible.  **No representation of the tail can change the reach.**  Neither route
was run, and that is stated rather than implied.

**F4. Integration by parts — helps only where it cannot.**  IBP is exact (verified to
`4.5e−7`), trading `R` for `R′` and gaining `1/x`.  But `∫|R′| = 6.288e−02` against
`∫|R| = 1.142e−02`, so the crossover is `x = 2.753`; above it the central bound is already
the binding constraint.  Recorded, not used.

**F5. Antihelix — no new bound, and the reason is compiled.**  The `v ↔ p` swap leaves
`Φ(v+p)Φ(v−p)` invariant (`C3B12.antihelix_swap`), so `R`'s defining form is symmetric under
it (batch 14, `reldiff 0.00e+00`).

**F6. `π/3` — applicable here, tested, NOT privileged.**  Unlike batch 14 (where only moments
appeared), the window radius `a` **is** a coordinate in the cell-centre variable `v`, so the
register is genuinely checkable.  Measured: `K(π/3) = 3.858e−03`, `K(π/6) = 3.874e−03`,
`K(π/12) = 4.867e−03` against the free optimum `4.882e−03` at `x = 4`.  The `π/3` lattice is
**not** privileged for this quantity.  **A unit-1 scan was NOT run** — that is the documented
false-null trap.  Reported as a measured null.

**F7 (MINE, RETRACTED). Block 1's "method ceiling" section is defective twice over.**  It
printed *"CEILING of the absolute-tail window method: |x| ≤ 30.000000"*.
(i) The `30.0` is the **top of the binary-search range**, not a measurement: `T(a)` underflows
to exactly `0` in float64 for `a ≥ 0.75`, so `C(a,x) − 2T(a)` became literally `C(a,x)` and
the "ceiling" was the target itself.
(ii) The stated reason was **backwards**.  I claimed the tail limits the method.  It does not:
`T(0.5) = 2.03e−06`, `T(0.75) = 9.77e−11`.  What limits it is the **central** bound.  Both
corrected in block 2 §A, and the corrected statement is what appears above.

**F8 (MINE, RETRACTED prose). Block 2's `C` section header.**  It described the dyadic split
as bounding "each annulus by its own sup"; the code computes the annuli **exactly**, so the
printed description does not match the computation.  The measurement is unaffected (the split
is exact), but the prose is corrected here.

**F9. Higher-order Taylor central bounds gain little.**  `P6(z) = 1 − z²/2 + z⁴/24 − z⁶/720`
and `P10` were **verified to be valid global lower bounds** (`min(cos − P) ≥ −2.3e−16` over
`|z| ≤ 60`) before use.  Reach: `P2 → 6.638679`, `P6 → 6.805123`, a gain of `+0.166`.  Not
formalised — the gain does not justify the extra moments.

---

## HOSTILE NUMERICS

**H3 — cancellation-free scan at 40 dps** (`L₁(x) = Ξ(x)²·(ξ′/ξ)′(½+ix)`, never a finite
difference), **2065 points**: a `5e−5` grid on `[0,0.1]` (near zero), step `0.02` on
`[0.1,10]` (transitions), step `0.1` on `[10,60]`, step `0.5` on `[60,400]`, plus **27 known
zero ordinates × 7 offsets** `{0, ±1e−10, ±1e−4, ±0.05}`.

```
  NEGATIVES of L1/Xi^2: 0
  min L1/Xi^2 = 0.0462099862308 at x = 0.0
```

Control: `cosMom R 0` from the float64 grid vs `L₁(0)` at 40 dps — `reldiff 7.6e−16`.

---

## CHART AUDIT

| chart | preserved how in batch 15 |
|---|---|
| **native helix `Re s > 0`, phasors from 0** | No convergence abscissa anywhere. Every integrability fact is domination on a bounded window or `\|cos\| ≤ 1`. |
| **physical carrier `Z > 0`, `y = log Z`** | The window radius `a` and the variable `v` are cell-centre coordinates in the `t = log Z` chart; `Ioo(-a,a)` and `Ioi a` are carrier sets. |
| **double helix / anti-helix conjugation** | `tail_reflect` **is** the conjugation used constructively: the left tail equals the right tail because `R` is even, which is `C3B14.Rker_even`, which is the Jacobi reflection. §F5 records that the `v ↔ p` swap gives nothing further. |
| **`S(t) = N_{π/3}(e^t) − N_1(e^t)` as a registration gap, not a unit-1 cell scan** | §F6: because `a` is a genuine cell coordinate here, the register **was** tested — and found not privileged. **No unit-1 scan was run.** No count is formed anywhere in this batch, so `S(t)` itself is untouched and unblended. |
| **`Ξ` chart** | `Ξ(x) = ξ(½+ix)`, `cosMom riemannXiKernel x = 2Ξ(x)`; kept distinct from `hp_pencil_v2`'s and `XiStructureFunction`'s conjugate charts. |
| **GRH family charts** | Untouched; `Rker` is built from `riemannXiKernel` alone. **No GRH statement follows.** |

The C3 campaign remains **not in print**; no paper edit is proposed.

---

## THE SMALLEST NEXT LEAN THEOREM

The compiled criterion's reach is capped by `Q(a)` alone (`criterion_forces_x_bound`).  The
smallest statement that lifts that cap is a **non-polynomial central minorant** with a
computable moment.  The Gaussian minorant is the cheapest, and it needs only one elementary
inequality:

```lean
theorem central_ge_gauss (a x : ℝ) (β : ℝ) (hβ : 0 < β) :
    (∫ v in Ioo (-a) a, Rker v * Real.exp (-β * (2*x*v)^2)) - 2 * (∫ v in Ioo (-a) a, Rker v)
      ≤ ∫ v in Ioo (-a) a, Rker v * Real.cos (2 * x * v)
```

i.e. `cos z ≥ 2e^{−βz²} − 2` for a suitable `β` — a bounded minorant that, unlike every
polynomial, **decays instead of diverging**, so the resulting criterion is not capped by a
moment.  It is one pointwise inequality plus the same window machinery already compiled here.
Stated honestly: this is a **reduction step**, and the prediction recorded above is that it
extends the reach without removing the cap, because the tail term stays `x`-independent.

---

## MACHINE-READABLE SUMMARY

```yaml
batch: c3-batch-15
date: 2026-08-25
branch: ladder-campaign-2026-08
target_proved: false
rh_claimed: false
grh_claimed: false
novelty_claimed: false
commits: 0
tracked_files_modified: 0
lean_files_new: 2
declarations_compiled: 19
declarations_by_file: {A1: 10, A2: 9}
axiom_footprint_all: "[propext, Classical.choice, Quot.sound]"
audit_log: tmp/c3b15_audit.log
forbidden_pattern_scan: "clean (exit 1, no output) over c3b15_A1, c3b15_A2"
batch14_correction: "its proposed cosMom_Rker_window carried an extra factor 2 on the central Ioo(-a,a) integral. FALSE: at x=0, a->infinity it asserts S <= 0 for S = 0.00571 > 0. RETRACTED in place and replaced. Orientation re-tested over 30 hostile (a,x) pairs: old form violated 24 times, corrected form 0."
decompositions_run: 21
headline:
  name: C3B15.window_criterion_quadratic
  statement: "2 x^2 Qwin a + 4 Tail a <= cosMom Rker 0  =>  0 <= cosMom Rker (2 x)"
  character: "every quantity is an explicit integral of the nonnegative kernel R; the hypothesis mentions neither the target nor Xi nor any zero"
  reach: 6.638679
  coverage_0_60: "133/1201 = 11.07%"
  prior_best: "batch 13 |x| <= 2.503 (4.41%); batch 12 the single point x = 0"
supporting:
  - "C3B15.window_lower_tail: the CORRECTED window bound, via tail_reflect (even-tail change of variables, Mathlib integral_comp_neg_Iic + C3B14.Rker_even)"
  - "C3B15.central_ge_quadratic: Real.one_sub_sq_div_two_le_cos, valid for ALL x and a"
  - "C3B15.central_ge_linear: Real.one_sub_mul_le_cos on 2|x|a <= pi/2, exact at z = pi/2 where the quadratic gives -0.2337"
  - "C3B15.compl_mass, window_mass: the identities that make the criterion three computable numbers"
uniform_a_of_x:
  attempted: true
  outcome: "PER-a CAP COMPILED; GLOBAL ADAPTIVE-WINDOW EXCLUSION IS **UNCOMPILED**"
  corrected: "2026-08-25 OpenAI adjudication. The compiled theorems give FOR EACH FIXED a a cap x^2 <= mass/(2 Qwin a). That is (forall a)(exists cap), NOT (exists cap)(forall a); it does not exclude an adaptive a(x) whose cap grows with x. The stronger conclusion needs Tail antitone, Qwin monotone on a >= 0, AND a uniform positive lower bound for Qwin over {a : 4 Tail a <= mass}. None of those was compiled in batch 15."
  theorems: ["criterion_needs_small_tail: forces 4 T(a) <= mass, so a cannot shrink",
             "criterion_forces_x_bound: forces x^2 <= mass/(2 Qwin a), a finite cap PER FIXED a"]
  reason: "a polynomial minorant cos z >= P(z) has P -> -infinity while the true central integral decays like e^{-pi x/2}; no polynomial tracks exponential decay"
  cheapest_refutation_not_run: "a non-polynomial (Gaussian) central minorant with a computable moment"
retractions_this_batch:
  - "F7 (mine): block 1's 'method ceiling |x| <= 30' was the top of the binary-search range, not a measurement (T(a) underflows to 0 for a >= 0.75); AND its stated reason was backwards -- the tail is doubly-exponentially small, the CENTRAL bound is what binds."
  - "F8 (mine): block 2's dyadic-annuli prose said 'bounded by its own sup' while the code computes the annuli exactly."
verified_before_formalising:
  - "both central bounds checked <= the exact central integral at nine (a,x) pairs"
  - "P6 and P10 verified to be valid global lower bounds (min(cos - P) >= -2.3e-16 over |z| <= 60) before any use"
  - "Chernoff inequality LHS <= RHS verified at five lambda before being recorded"
hostile_scan:
  points: 2065
  grid: "5e-5 near zero on [0,0.1]; 0.02 on [0.1,10]; 0.1 on [10,60]; 0.5 on [60,400]; 27 zero ordinates x 7 offsets"
  method: "cancellation-free, L1 = Xi^2 (xi'/xi)'(1/2+ix) at 40 dps, never a finite difference"
  negatives: 0
  min_scale_free: 0.0462099862308
  control: "cosMom R 0 float64 vs L1(0) at 40 dps, reldiff 7.6e-16"
pi3_register:
  applicable: true
  reason: "the window radius a IS a cell-centre coordinate here, unlike batch 14 where only moments appeared"
  result: "measured NOT privileged: K(pi/3)=3.858e-03, K(pi/6)=3.874e-03, K(pi/12)=4.867e-03 vs free optimum 4.882e-03 at x=4"
  unit_one_scan_run: false
literature_check_still_required:
  - "first Laguerre inequality for the Riemann Xi function: NOT read at source (web tools unavailable, FIVE sessions running). NO novelty claimed anywhere."
open_next_lean_statement: |
  theorem central_ge_gauss (a x : R) (beta : R) (hbeta : 0 < beta) :
      (int v in Ioo (-a) a, Rker v * Real.exp (-beta * (2*x*v)^2))
        - 2 * (int v in Ioo (-a) a, Rker v)
        <= int v in Ioo (-a) a, Rker v * Real.cos (2*x*v)
open_next_purpose: "a NON-POLYNOMIAL central minorant (cos z >= 2 exp(-beta z^2) - 2), which decays instead of diverging, so the resulting criterion is not capped by a moment. One pointwise inequality plus the window machinery already compiled. Predicted to extend the reach but not remove the cap, since the tail term is x-independent."
```
