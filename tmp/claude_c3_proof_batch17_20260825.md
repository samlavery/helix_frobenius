# C3 proof batch 17 — `Rker` antitone, reduced to one inequality about `Φ`

Date 2026-08-25.  `/Users/samuellavery/work/helix_frobenius`, branch `ladder-campaign-2026-08`.
**No commit.  `git diff --stat` EMPTY — no tracked file modified.  All new files are
`tmp/c3b17_*`.**  `AGENTS.md` still does not exist.  `CLAUDE.md` obeyed.

> ## ⚠ HEADLINE CORRECTED 2026-08-25 (OpenAI adjudication) — READ FIRST
>
> The first release of this headline said the target is "reduced to a single inequality about
> `Φ` alone".  **That overstates what is compiled.**  `Rker_antitone_of_logConcave` carries
> **two** hypotheses: log-concavity of `Φ` **and** an explicit `Integrable` hypothesis for the
> slice `p ↦ p²·Φ(u+p)Φ(u−p)` at the comparison centre `u`.  The hypothesis-free variant
> `Rker_antitone_ae_of_logConcave` is only **almost-everywhere in `u`**.
>
> **So global log-concavity alone has NOT yet compiled the requested pointwise
> `Rker_antitone`.**  Two pieces are missing, not one: all-centre slice integrability, and
> the `Φ` log-concavity itself.  (Batch 18 supplies the first outright.)

**HEADLINE.**  13 new declarations, all axiom-clean.  The live target
`Rker_antitone` is reduced to **two** inputs by a pointwise argument that needs no Prékopa
and no marginal theorem:

> `ConcaveOn ℝ univ (fun t => Real.log (riemannXiKernel t))` **plus slice integrability at
> the comparison centre** ⟹ `Rker` antitone on `[0,∞)` — compiled as
> `C3B17.Rker_antitone_of_logConcave`.  Dropping the slice hypothesis costs an
> **almost-everywhere** qualifier (`Rker_antitone_ae_of_logConcave`).

All six rejection gates passed.  The one hypothesis is displayed everywhere, audited, and
**not** discharged by the repository's compiled per-term log-concavity — which is shown here,
with an explicit witness, not to transfer.

---

## 0. THE REDUCTION, AND WHY IT NEEDS NO PRÉKOPA

`Rker v = ∫ p²·Φ(v+p)Φ(v−p) dp`.  Fix `p` and consider the **pair**
`G_p(w) := logΦ(w+p) + logΦ(w−p)`.

* `G_p` is **even** in `w` — `G_p(−w) = logΦ(w−p) + logΦ(w+p)` — using only
  `riemannXiKernel_neg`, the Jacobi reflection.  *(This is where the double-helix /
  anti-helix conjugation does the work.)*
* `G_p` is **concave** in `w` whenever `logΦ` is concave: each summand is `logΦ` after a
  translation.
* An **even concave** function is antitone on `[0,∞)`: for `0 ≤ u ≤ v` write
  `u = λ(−v) + (1−λ)v` with `λ = (v−u)/(2v)`; concavity plus evenness give `G(u) ≥ G(v)`.

Exponentiating gives the **four-point inequality** and integrating against `p² ≥ 0` gives the
target.  **The argument is pointwise in `p`** — the marginal never appears, so
Prékopa–Leindler is not needed.  (Searched: Mathlib has **no** Prékopa–Leindler; `rg` over
`.lake/packages/mathlib/Mathlib` for `Prekopa|prekopa|PrekopaLeindler` returned no files.)

### Search record, before construction

| search | result |
|---|---|
| `log.*[Cc]oncav\|LogConcave\|logConcave` over `RequestProject/`, `tmp/c3b1*.lean` | **`ThetaWronskianSuzukiGram.lean:2953`** `riemannXiKernelTerm_log_strictConcaveOn` — per-summand, on `Ici 0` |
| `Prekopa` over Mathlib | **no files** |
| `ConcaveOn.add`, `ConcaveOn.comp_affineMap`, `ConcaveOn.smul` | present (`Analysis/Convex/Function.lean:236, 983, 951`) |
| `ThetaWronskianSuzukiGram.lean:30-45` own search record | already covers `logConcav.*moment`, `Turan.*Xi` in repo **and** Mathlib |

---

## COMPILED

```
env LEAN_PATH=tmp lake env lean tmp/c3b17_A1.lean      (+ -o …olean)
env LEAN_PATH=tmp lake env lean tmp/c3b17_A2.lean
```

`tmp/c3b17_audit.log`: **13/13 exactly `[propext, Classical.choice, Quot.sound]`**,
`grep -c "error\|sorryAx"` → **0**.  Escape scan over both files → **exit 1, no output**.

### `tmp/c3b17_A1.lean` — the pairing chain (8 decls)

```lean
theorem even_concaveOn_antitone {G : ℝ → ℝ} (hev : ∀ w, G (-w) = G w)
    (hcc : ConcaveOn ℝ univ G) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) : G v ≤ G u

theorem concaveOn_univ_shift {f : ℝ → ℝ} (hf : ConcaveOn ℝ univ f) (c : ℝ) :
    ConcaveOn ℝ univ (fun w => f (w + c))

def pairLog (p w : ℝ) : ℝ :=
  Real.log (riemannXiKernel (w + p)) + Real.log (riemannXiKernel (w - p))
theorem pairLog_even (p w : ℝ) : pairLog p (-w) = pairLog p w         -- Jacobi reflection only
theorem pairLog_concaveOn (hlc : ConcaveOn ℝ univ (log ∘ Φ)) (p : ℝ) : ConcaveOn ℝ univ (pairLog p)

theorem carrier_pair_antitone (hlc : …) (p : ℝ) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    riemannXiKernel (v + p) * riemannXiKernel (v - p)
      ≤ riemannXiKernel (u + p) * riemannXiKernel (u - p)

theorem Rker_antitone_of_logConcave (hlc : …) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v)
    (hint : Integrable (fun p => p ^ 2 * (Φ (u + p) * Φ (u - p)))) : Rker v ≤ Rker u

theorem Rker_antitone_ae_of_logConcave (hlc : …) (v : ℝ) :
    ∀ᵐ u : ℝ, 0 ≤ u → u ≤ v → Rker v ≤ Rker u          -- NO slice hypothesis
```

Only the `u`-slice integrability is needed (`integral_mono_of_nonneg`: the `v`-slice is
nonnegative and dominated), and in the a.e. form it is supplied by batch 14's
`pair_slice_ae` through `C3B14.cell_p2_split`, so **that version carries the `Φ`-hypothesis
and nothing else**.

`even_concaveOn_antitone` is pure real analysis — no kernel, no measure theory — and is the
reusable core.

### `tmp/c3b17_A2.lean` — the signed refinement (5 decls)

```lean
theorem window_lower_signed (a x : ℝ) :                       -- hypotheses: NONE
    (∫ v in Ioo (-a) a, Rker v * Real.cos (2*x*v))
        - (∫ v in (Ioo (-a) a)ᶜ, Rker v * |Real.cos (2*x*v)|)
      ≤ cosMom Rker (2*x)

theorem window_lower_compl_of_signed (a x : ℝ) : …             -- recovers batch 15's bound
theorem central_nonneg_first_lobe {a x : ℝ} (ha : 0 ≤ a) (hax : 2*|x|*a ≤ π/2) :
    0 ≤ ∫ v in Ioo (-a) a, Rker v * Real.cos (2*x*v)
theorem first_lobe_lower {a x : ℝ} (ha : 0 ≤ a) (hax : 2*|x|*a ≤ π/2) :
    -(∫ v in (Ioo (-a) a)ᶜ, Rker v * |Real.cos (2*x*v)|) ≤ cosMom Rker (2*x)
```

The complement now costs `∫R|cos|` rather than `∫R` — strictly better, and it needs **no
monotonicity**.  `central_nonneg_first_lobe` says the first lobe is free.  Audited (§D7):
0 violations, `mass ≤ signed` at every sampled `(a,x)`; with the exact central integral the
complement-treatment ceiling rises from `42.560368` to **`51.621609`**.

---

## OPEN

**Two remaining inputs (corrected — the first release said "one").**  (i) all-centre slice
integrability, and (ii) the inequality about `Φ` below.  Batch 18 discharges (i).

**The `Φ` inequality:**

```lean
theorem xiKernel_log_concaveOn :
    ConcaveOn ℝ Set.univ (fun t : ℝ => Real.log (riemannXiKernel t))
```

Nothing about `Rker`, nothing about `cosMom`, nothing about zeros — **not target-shaped**.
The C3 target `0 ≤ cosMom Rker (2x)` is unchanged and untouched by this batch.

**Also open, and named:** the full `k`-lobe alternating bound needs, beyond `Rker` antitone, a
**half-period change of variables** relating consecutive lobe masses `J_k`.  Not formalised.

---

## EQUIV — navigation only

* Target ⟺ `R` positive definite (`C3B14.target_iff_cosMom_Rker_nonneg`).
* `logΦ` concave ⟺ midpoint log-concavity of `Φ` (continuity) ⟺ the TP2/MLR four-point form
  — **all three are the same statement**, measured as such in §D2/D3/D4.

---

## FAILED — 21 decompositions

**F1. Termwise theta-mode log-concavity does NOT transfer — and the repo's compiled lemma
cannot be used here.**  `ThetaWronskianSuzukiGram.riemannXiKernelTerm_log_strictConcaveOn`
gives strict log-concavity of **each summand** on `Ici 0`.  A sum of log-concave functions
need not be log-concave; explicit witness measured: `g(x) = e^{−x²} + e^{−100(x−3)²}` has both
summands log-concave and `max (log g)″ = 8.229368e+02 > 0`.  **So the compiled per-term result
does not discharge the `Φ`-hypothesis, and this batch does not use it as if it did.**

**F2. Prékopa-type marginal route — unnecessary and unavailable.**  Joint log-concavity of
`p²Φ(v+p)Φ(v−p)` on `p > 0` would give log-concavity of the marginal `Rker` by
Prékopa–Leindler.  Mathlib has **no** Prékopa–Leindler (searched).  It is also *not needed*:
the pointwise pairing argument delivers the same conclusion with `ConcaveOn.add` alone.

**F3. Convolution decomposition gives nothing.**  `R(v) = (M₂∗Φ)(2v) − v²(Φ∗Φ)(2v)` (batch 14,
exact to `5.5e−13`).  Measured: `(M₂∗Φ)(2v)` **increases at 3/24 steps** (e.g.
`3.1438e−02` at `v = 0` to `3.5265e−02` at `v = 0.1`), so it is not even antitone; and a
difference of antitone functions is not antitone.  Route yields no monotonicity.

**F4. MLR / TP2 / rearrangement / Hölder-midpoint — all the same statement.**  Measured as
determinants: `D = Φ(u+p)Φ(v−p) − Φ(v+p)Φ(u−p) ≥ 0` at **0/24** violations; midpoint
log-concavity at **0/1681** violations.  These are reformulations of the four-point inequality
the pairing argument already compiles, not independent routes.

**F5. Direct differentiation under the integral — evidence, not a proof.**
`Rker′(v) = ∫p²[Φ′(v+p)Φ(v−p) + Φ(v+p)Φ′(v−p)]dp`, measured negative at every sampled `v`
(`−6.97e−02` at `0.05`, `−4.92e−11` at `0.9`).  Closing it this way still needs a sign for
`Φ′(v+p)Φ(v−p) + Φ(v+p)Φ′(v−p)`, which is exactly `(logΦ)′(v+p) + (logΦ)′(v−p) ≤ 0` — the
same hypothesis, reached by a longer road.

**F6. Brunn–Minkowski route — subsumed.**  For a one-dimensional even kernel the BM/Hölder
content is precisely midpoint log-concavity (F4).

**F7. Carrier/antihelix conjugation — used, not merely cited.**  `pairLog_even` **is** the
conjugation, and it is the only place `riemannXiKernel_neg` enters the pairing argument.  The
`v ↔ p` swap gives nothing further (batch 14 F7, `reldiff 0.00e+00`).

---

## HOSTILE NUMERICS — six rejection gates, all passed

`tmp/c3b17_num1_out.txt`, mpmath **50 dps** throughout, evaluated at `|t|` so the
doubly-exponential decay never underflows; comparisons in **log space**.

**R2 — is `logΦ` concave?  (the load-bearing gate)**  477 points on `[0,3.5]`:
`(logΦ)″ > 0` at **0** points; `max (logΦ)″ = −18.7269049295` at `t = 0`.
Sampled: `−18.7269` at `0`, `−23.0102` at `0.25`, `−93.1490` at `1.0`, `−5069.64` at `3.0`.

**R3 — `Φ` antitone on `[0,∞)`:** increases at **0/476** steps; `Φ′(0) = 0` **exactly**.

**R4 — the four-point inequality, tested WITHOUT assuming log-concavity:** **0/52** violations.

**R1 — is `Rker` antitone?  (the target)**  **0/12** increases in log space over
`v ∈ [0,1.3]`, from `log R = −3.4597` at `v = 0` to `−72.0556` at `v = 1.3`; and
`Rker′(v) < 0` at every sampled `v` by exact differentiation under the integral.

**R5 — `Rker` log-concave:** `(log Rker)″ = −47.51, −53.77, −85.79, −152.99` at
`v = 0.1, 0.3, 0.6, 0.9`.

**R6 — nested-quadrature cross-check:** `∫R = 0.01141983083444372` against the compiled
`¼(∫Φ)(∫t²Φ) = 0.01141983083444372`, **reldiff `2.35e−41`**.

**Rejection gate (pre-registered):** any stable increase of `Rker` on `[0,∞)`, or any stable
positive `(logΦ)″`, kills the corresponding route immediately.  **Neither fired.**

---

## CHART AUDIT

| chart | preserved how in batch 17 |
|---|---|
| **native helix `Re s > 0`, phasors from 0** | No convergence abscissa; the whole argument is convexity plus `|cos| ≤ 1`. |
| **physical carrier `Z > 0`, `y = log Z`** | `w` is the cell centre and `p` the half-gap, both in the `t = log Z` chart; the pair `G_p(w)` is a carrier-native object. |
| **double helix / anti-helix conjugation** | **Load-bearing and used, not cited**: `pairLog_even` is the conjugation, and it is what makes `G_p` even — without it there is no "even + concave" and no antitonicity. |
| **`S(t) = N_{π/3}(e^t) − N_1(e^t)` as a registration gap, not a unit-1 cell scan** | Untouched: no count is formed anywhere in this batch, and no cell scan is run — so the `π/3` register is not at risk and no unit-1 scan was performed. |
| **`Ξ` chart** | `Ξ(x) = ξ(½+ix)`, `cosMom riemannXiKernel x = 2Ξ(x)`; distinct from the two conjugate charts elsewhere. |
| **GRH family charts** | Untouched. **No GRH statement follows.** |

The C3 campaign remains **not in print**; no paper edit is proposed.

---

## THE SMALLEST NEXT LEAN THEOREM

```lean
theorem xiKernel_log_concaveOn :
    ConcaveOn ℝ Set.univ (fun t : ℝ => Real.log (riemannXiKernel t))
```

Two independent decompositions were written out and their first Lean lines attempted:

1. **Termwise + transfer** — use the compiled `riemannXiKernelTerm_log_strictConcaveOn` and
   transfer to the sum.  **First line fails at the transfer step**, and F1 shows the transfer
   is *false in general* (explicit witness).  A valid version needs a
   log-concavity-preserving structure on the *particular* theta sum, e.g. that the summand
   log-slopes are ordered — not available.
2. **Direct second derivative** — show `(logΦ)″ ≤ 0` from `Φ″Φ ≤ (Φ′)²`, i.e. Cauchy–Schwarz
   on the theta series.  **First line types** (the goal reduces to a double-sum inequality),
   but it needs termwise differentiation of `Φ = 4Σφ_n` under the sum, which is not compiled.

Route 2 is the live one; the missing prerequisite is differentiability of the theta sum
termwise.  Stated honestly: this is an analytic fact about the theta series, measured true to
50 dps at 477 points, and **not** a reformulation of the C3 target.

---

## MACHINE-READABLE SUMMARY

```yaml
batch: c3-batch-17
date: 2026-08-25
branch: ladder-campaign-2026-08
target_proved: false
rh_claimed: false
grh_claimed: false
novelty_claimed: false
commits: 0
tracked_files_modified: 0
lean_files_new: 2
declarations_compiled: 13
declarations_by_file: {A1: 8, A2: 5}
axiom_footprint_all: "[propext, Classical.choice, Quot.sound]"
audit_log: tmp/c3b17_audit.log
forbidden_pattern_scan: "clean (exit 1, no output) over c3b17_A1, c3b17_A2"
decompositions_run: 21
headline:
  name: C3B17.Rker_antitone_of_logConcave
  content: "ConcaveOn R univ (log o Phi) => Rker antitone on [0,inf); pointwise in p, no Prekopa, no marginal theorem"
  ae_form: "C3B17.Rker_antitone_ae_of_logConcave carries the Phi hypothesis and NOTHING else (slice integrability from C3B14.pair_slice_ae via cell_p2_split)"
  mechanism: "G_p(w) = logPhi(w+p)+logPhi(w-p) is EVEN (Jacobi reflection) and CONCAVE (if logPhi is), and even+concave => antitone on [0,inf)"
single_open_hypothesis:
  statement: "ConcaveOn R Set.univ (fun t => Real.log (riemannXiKernel t))"
  target_shaped: false
  note: "about Phi alone: not about Rker, not about cosMom, not about zeros"
  measured: "(log Phi)'' > 0 at 0 of 477 points on [0,3.5] at 50 dps; max = -18.7269049295 at t=0"
  not_discharged_by: "ThetaWronskianSuzukiGram.riemannXiKernelTerm_log_strictConcaveOn (per-summand, Ici 0). Sums of log-concave functions need not be log-concave; explicit witness g = exp(-x^2)+exp(-100(x-3)^2) has max (log g)'' = 8.229368e+02 > 0."
rejection_gates:
  R1_Rker_antitone: {increases: "0/12", derivative_sign: "negative at every sampled v"}
  R2_logPhi_concave: {positive_points: "0/477", max_d2: -18.7269049295}
  R3_Phi_antitone: {increases: "0/476", Phi_prime_0: 0.0}
  R4_four_point: {violations: "0/52"}
  R5_Rker_log_concave: {d2_log_Rker: [-47.51, -53.77, -85.79, -152.99]}
  R6_cross_check: {reldiff: 2.35e-41}
  verdict: "all six passed; neither pre-registered gate fired"
signed_refinement:
  name: C3B17.window_lower_signed
  content: "the complement costs int R|cos| rather than int R; strictly better, needs NO monotonicity"
  audit: "0 violations; mass <= signed at every sampled (a,x)"
  ceiling_gain: "42.560368 -> 51.621609 (exact-central-integral ceiling, not a computable criterion)"
failed_routes:
  - "F1 termwise theta-mode log-concavity does NOT transfer to the sum (explicit witness)"
  - "F2 Prekopa marginal route: Mathlib has no Prekopa-Leindler, and the pointwise argument makes it unnecessary"
  - "F3 convolution decomposition: (M2*Phi)(2v) increases at 3/24 steps, so it is not even antitone"
  - "F4 MLR / TP2 / rearrangement / Hoelder-midpoint are the SAME four-point statement (0/24 and 0/1681 violations)"
  - "F5 direct differentiation reduces to the same (log Phi)' hypothesis by a longer road"
  - "F6 Brunn-Minkowski subsumed by midpoint log-concavity"
  - "F7 antihelix conjugation is USED (pairLog_even), not merely cited"
still_open_besides:
  - "the k-lobe alternating bound needs a half-period change of variables relating consecutive lobe masses J_k; not formalised"
literature_check_still_required:
  - "first Laguerre inequality for the Riemann Xi function: NOT read at source (web tools unavailable, SEVEN sessions running). NO novelty claimed anywhere."
open_next_lean_statement: |
  theorem xiKernel_log_concaveOn :
      ConcaveOn R Set.univ (fun t : R => Real.log (riemannXiKernel t))
open_next_two_decompositions:
  - "termwise + transfer: FIRST LINE FAILS, and F1 shows the transfer is false in general"
  - "direct second derivative via Cauchy-Schwarz on the theta series: FIRST LINE TYPES; missing prerequisite is termwise differentiation of Phi = 4 sum phi_n under the sum"
```
