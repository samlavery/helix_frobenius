# C3 proof batch 18 — all-centre integrability closed; `Φ` log-concavity reduced to one double sum

Date 2026-08-25.  `/Users/samuellavery/work/helix_frobenius`, branch `ladder-campaign-2026-08`.
**No commit.  `git diff --stat` EMPTY — no tracked file modified.  All new files are
`tmp/c3b18_*`.**  `AGENTS.md` still does not exist.  `CLAUDE.md` obeyed.

**HEADLINE.**  15 new declarations, all axiom-clean.  Of the **two** missing pieces the
adjudication identified, **one is closed outright**:

> `C3B18.pair_slice_integrable (u : ℝ) :`
> `Integrable (fun p => p² * (Φ(u+p) * Φ(u−p)))` — **every centre, no Fubini, no a.e.**
>
> hence `C3B18.Rker_antitone_of_logConcave'` : the pointwise `Rker` antitonicity whose **only**
> remaining hypothesis is about `Φ`.

And the signed-lobe lemma batch 17 named as missing is compiled: `lobe_block_antitone`.

---

## 0. CORRECTION TO BATCH 17, APPLIED BEFORE NEW WORK

Batch 17's headline said the target is "reduced to a **single** inequality about `Φ` alone".
**That overstated what was compiled.**  `Rker_antitone_of_logConcave` carries **two**
hypotheses — log-concavity of `Φ` *and* an explicit `Integrable` hypothesis for the slice
`p ↦ p²Φ(u+p)Φ(u−p)` at the comparison centre `u`; the hypothesis-free variant is only
**almost-everywhere in `u`** (it routes through `C3B14.pair_slice_ae`, a Fubini statement that
names no particular `u`).  Corrected in place in
`tmp/claude_c3_proof_batch17_20260825.md` (headline and OPEN section).  **No theorem statement
changed**; all 13 batch-17 declarations recompile clean.

---

## COMPILED

```
env LEAN_PATH=tmp lake env lean tmp/c3b18_A1.lean      (+ -o …olean)
env LEAN_PATH=tmp lake env lean tmp/c3b18_A2.lean      (+ -o …olean)
env LEAN_PATH=tmp lake env lean tmp/c3b18_A3.lean
```

`tmp/c3b18_audit.log`: **15/15 exactly `[propext, Classical.choice, Quot.sound]`**,
`grep -c "error\|sorryAx"` → **0**.  Escape scan over all three files → **exit 1, no output**.

### `tmp/c3b18_A1.lean` — all-centre slice integrability (7 decls)

```lean
theorem xiKernel_le_const (t : ℝ) : riemannXiKernel t ≤ xiKernelMajorantConstant
theorem shifted_sq_xiKernel_integrable (u : ℝ) :
    Integrable (fun q => (u - q) ^ 2 * riemannXiKernel q)
theorem sq_xiKernel_reflect_integrable (u : ℝ) :
    Integrable (fun p => p ^ 2 * riemannXiKernel (u - p))
theorem pair_slice_integrable (u : ℝ) :                       -- EVERY centre
    Integrable (fun p => p ^ 2 * (riemannXiKernel (u + p) * riemannXiKernel (u - p)))

theorem Rker_antitone_of_logConcave'
    (hlc : ConcaveOn ℝ univ (fun t => Real.log (riemannXiKernel t)))
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) : Rker v ≤ Rker u
theorem Rker_antitoneOn_of_logConcave (hlc : …) : AntitoneOn Rker (Ici 0)
```

**Mechanism — an explicit majorant, not Fubini.**  The repository already proves
`riemannXiKernel_le_majorant (hu : 0 ≤ u) : Φ u ≤ C·exp(−3u/2)` with
`C = xiKernelMajorantConstant ≥ 0`.  Since `exp(−3u/2) ≤ 1` on `u ≥ 0`, that gives `Φ ≤ C` on
`[0,∞)`; and `Φ` is **even** (`riemannXiKernel_neg`, the Jacobi reflection), so `Φ ≤ C` on the
whole line.  Then `p²Φ(u+p)Φ(u−p) ≤ C·p²Φ(u−p)`, and `p ↦ p²Φ(u−p)` is integrable because
`(u−q)²Φ(q) = u²Φ(q) − 2u·kM1(q) + kM2(q)` is a combination of the three compiled moments,
then reflected and translated.

**Search record before construction** (batches 10–14 and Mathlib, for reusable
shifted-product and polynomial-weight integrability): found and used
`C3B12.xiKernel_integrable`, `C3B12.kM1_integrable`, `C3B12.kM2_integrable`,
`riemannXiKernel_neg`, `riemannXiKernel_le_majorant`, `xiKernelMajorantConstant_nonneg`.
`C3B14.pair_slice_ae` is the a.e. Fubini route and is **deliberately not used**.

### `tmp/c3b18_A2.lean` — the signed-lobe lemma antitonicity unlocks (3 decls)

```lean
theorem abs_cos_half_period {x : ℝ} (hx : x ≠ 0) (v : ℝ) :
    |Real.cos (2*x*(v + Real.pi/(2*x)))| = |Real.cos (2*x*v)|

theorem lobe_block_antitone (hlc : …) {x : ℝ} (hx : 0 < x) {c : ℝ} (hc : 0 ≤ c) :
    (∫ v in (c + π/(2*x))..(c + π/x), Rker v * |Real.cos (2*x*v)|)
      ≤ ∫ v in c..(c + π/(2*x)), Rker v * |Real.cos (2*x*v)|
theorem lobe_block_antitone_succ (hlc : …) (hx : 0 < x) (k : ℕ) : …
```

Batch 17 named the missing ingredient as *"a half-period change of variables relating
consecutive lobe masses"*.  It is **just a translation**: `|cos(2xv)|` has half period
`π/(2x)`, and `Rker(v + π/(2x)) ≤ Rker v` by antitonicity, so block `k+1` is dominated by
block `k`.

> **Stated, not hidden:** the *first* block is special — it has **half** the length of the
> others — so `J₀ ≥ J₁` is **not** implied by this lemma.  Batch 16 measured `J₀ − J₁ < 0` for
> `x ≳ 8.86`, consistent with that.  Assembling the full alternating bound also needs an
> alternating-series argument over infinitely many blocks; **not formalised**.

### `tmp/c3b18_A3.lean` — the exact remaining double sum (5 decls)

```lean
theorem prod_sum_sub_eq_double (s : Finset ℕ) (a b c : ℕ → ℝ) :
    (∑ n ∈ s, a n) * (∑ n ∈ s, a n) - (∑ n ∈ s, b n) * (∑ n ∈ s, c n)
      = ∑ n ∈ s, ∑ m ∈ s, (a n * a m - b n * c m)
theorem double_sum_diag_offdiag (s : Finset ℕ) (f : ℕ → ℕ → ℝ) :
    (∑ n ∈ s, ∑ m ∈ s, f n m) = (∑ n ∈ s, f n n) + ∑ n ∈ s, ∑ m ∈ s.erase n, f n m
theorem midpoint_nonneg_of_diag_dominates (s : Finset ℕ) (a b c : ℕ → ℝ) (h : …) : …
```

With `a_n = a_n(t)`, `b_n = a_n(t−h)`, `c_n = a_n(t+h)` this is the exact decomposition of
`Φ(t)² − Φ(t−h)Φ(t+h)` into a **diagonal** part (nonnegative term by term — precisely the
repository's `riemannXiKernelTerm_log_strictConcaveOn`) and an **off-diagonal** part that is
**not** nonnegative.  The whole remaining content is that the diagonal surplus dominates.

---

## OPEN

```lean
theorem xiKernel_log_concaveOn :
    ConcaveOn ℝ Set.univ (fun t : ℝ => Real.log (riemannXiKernel t))
```

**Now the ONLY input** to pointwise `Rker` antitonicity — the integrability side is closed.
Not target-shaped: about `Φ` alone.  Also open and named: the alternating-series assembly of
the `k`-lobe bound, and the first-block asymmetry.

---

## EQUIV — navigation only

* Target ⟺ `R` positive definite (`C3B14.target_iff_cosMom_Rker_nonneg`).
* `logΦ` concave ⟺ midpoint log-concavity ⟺ hazard `−Φ′/Φ` nondecreasing ⟺ `ΦΦ″ ≤ (Φ′)²` —
  all four measured to agree (§T2, T5, T7).

---

## FAILED — 21 decompositions

**F1. Per-term log-concavity is NOT a mixture theorem — measured, not assumed.**  The
cross-pair inequality `2a_n(t)a_m(t) ≥ a_n(t−h)a_m(t+h) + a_m(t−h)a_n(t+h)` is violated at
**33/36** sampled `(n,m,t,h)`.  For log-linear terms `e^{αt}, e^{βt}` with `α ≠ β` the cross
term equals `2e^{(α+β)t}cosh((β−α)h) > 2e^{(α+β)t}`, so it is false in general.  **The
repository's compiled per-term theorem is therefore not used as a mixture theorem anywhere in
this batch.**

**F2. TP2 of the mode kernel fails in the stated orientation — 9/9.**  `a_n(t)a_m(s) −
a_n(s)a_m(t) < 0` for `n < m`, `t < s` at every sampled point (e.g. `−1.33e−04` at
`n,m = 1,2`, `t,s = 0.1,0.4`).  The family is totally positive in the *reversed* mode order
(higher modes decay faster).  Either way it does **not** yield log-concavity of the sum, which
F1 already settles.

**F3. Direct Prékopa/marginal route — still unavailable and still unnecessary** (batch 17 F2;
Mathlib has no Prékopa–Leindler).

**F4. `J₀ ≥ J₁` is NOT delivered by the block lemma.**  The first block is half-length.
Measured sign change at `x ≈ 8.863` (batch 16 §P4).  Recorded as a limitation of
`lobe_block_antitone`, not glossed.

**F5. Passage from Finset to tsum, and from midpoint to `ConcaveOn`, not formalised.**  The
first needs summability of the double series; the second needs continuity of `Φ` on the whole
line — the repository has `riemannXiKernel_continuousOn` on `Ici 0` **only**.  Both named.

---

## HOSTILE NUMERICS — gates, all passed

`tmp/c3b18_num1_out.txt`, mpmath **50 dps**, `t < 0` handled by **reflection** (exact and
fast; the raw series converges slowly there), comparisons in log space.

**T2 — `logΦ` concave on the FULL line.**  Three regimes, **724 points**, `(logΦ)″ > 0` at
**0**:

| regime | points | positive | max `(logΦ)″` |
|---|---|---|---|
| near 0, step `2e−3`, `|t| ≤ 0.2` | 201 | 0 | `−18.72690493` at `t=0` |
| transition, step `0.01`, `|t| ≤ 2` | 401 | 0 | `−18.72690493` at `t=0` |
| tail, step `0.05`, `2 ≤ |t| ≤ 5` | 122 | 0 | `−686.1361884` at `t=2` |

**T5 — variance form, coefficients audited.**  Termwise `Φ′` against `mpmath.diff` on the
summed kernel: `reldiff 0.0` at `t = 0.2, 0.7` and `1.3e−51` at `t = 1.3`.  Then
`ΦΦ″ − (Φ′)² < 0` at every sampled `t` (`−57.59` at `0.05` … `−3.78e−55` at `1.6`).

**T7 — hazard `−Φ′/Φ` nondecreasing:** **0** decreases over `t ∈ [−2,2]`, and `= 0` exactly at
`t = 0`.

**T3 — the double-sum split, and the margin.**  Split verified against the direct value to
`reldiff ≤ 1.5e−51`:

```
      t      h                   DIAG                    OFF             D=DIAG+OFF   D>=0
    0.1    0.3          2.25512176334       -0.0307369993831          2.22438476396   True
    0.4    0.3         0.111248694071        -1.835771676e-6         0.111246858299   True
    0.8    0.3       2.07375705096e-7     -8.59326356497e-20       2.07375705096e-7   True
    1.2   0.05      6.82968438207e-23     -4.08285201752e-62      6.82968438207e-23   True
```

`|OFF|/DIAG` runs `1.4e−2 → 1.6e−5 → 4.1e−13 → 6.0e−40`: the margin is enormous and **grows
with `t`**, so the tight region is small `t`.

**T1 — the bound that unlocks integrability:** `max Φ = 1.786787601868494` attained at `t = 0`
(consistent with evenness), and `Φ(1)/e^{−3/2} = 2.47e−6 ≤ C`.

**Rejection gate (pre-registered):** any stable positive `(logΦ)″` on the full line stops the
branch and is recorded as a counterexample.  **It did not fire.**

---

## CHART AUDIT

| chart | preserved how in batch 18 |
|---|---|
| **native helix `Re s > 0`, phasors from 0** | No convergence abscissa; the integrability argument is a pointwise majorant plus three compiled moments. |
| **physical carrier `Z > 0`, `y = log Z`** | `u` is the cell centre, `p` the half-gap, `c` a block boundary in `v` — all in the `t = log Z` chart. |
| **double helix / anti-helix conjugation** | **Load-bearing twice**: `Φ ≤ C` on the whole line comes from the half-line majorant *plus* `riemannXiKernel_neg`; and `pairLog_even` (batch 17) is the same reflection. |
| **`S(t) = N_{π/3}(e^t) − N_1(e^t)` as a registration gap, not a unit-1 cell scan** | Untouched: no count is formed, no cell scan run. Negative `t` is handled by the **Jacobi reflection**, which is an identity, not a registration choice. |
| **`Ξ` chart** | Unused this batch — everything is on `Φ` and `Rker` in the carrier variable. |
| **GRH family charts** | Untouched. **No GRH statement follows.** |

The C3 campaign remains **not in print**; no paper edit is proposed.

---

## THE SMALLEST NEXT LEAN THEOREM

The tight region is small `t` (T3), and the passage to `ConcaveOn` needs continuity on the
whole line, which the repository has only on `Ici 0`.  The smallest step that removes a named
blocker without touching the hard double sum:

```lean
theorem xiKernel_continuous : Continuous riemannXiKernel
```

from `riemannXiKernel_continuousOn` on `Ici 0` plus evenness (`riemannXiKernel_neg`) — a
gluing argument at `0`, where the two branches agree and the reflection is an identity.  It is
required for *any* passage from midpoint log-concavity to `ConcaveOn`, and it is independent
of the double-sum question, so it can be landed separately.  Stated honestly: this is a
prerequisite, not the main obstruction; the main obstruction remains the diagonal-dominates
inequality of §A3.

---

## MACHINE-READABLE SUMMARY

```yaml
batch: c3-batch-18
date: 2026-08-25
branch: ladder-campaign-2026-08
target_proved: false
rh_claimed: false
grh_claimed: false
novelty_claimed: false
commits: 0
tracked_files_modified: 0
lean_files_new: 3
declarations_compiled: 15
declarations_by_file: {A1: 7, A2: 3, A3: 5}
axiom_footprint_all: "[propext, Classical.choice, Quot.sound]"
audit_log: tmp/c3b18_audit.log
forbidden_pattern_scan: "clean (exit 1, no output) over c3b18_A1, A2, A3"
batch17_correction: "its headline said the target was reduced to a SINGLE inequality about Phi. Rker_antitone_of_logConcave in fact carries TWO hypotheses (log-concavity AND slice integrability at the comparison centre); the hypothesis-free variant is only a.e. in u. Corrected in place; no theorem statement changed; all 13 batch-17 declarations recompile clean."
decompositions_run: 21
piece_1_closed:
  name: C3B18.pair_slice_integrable
  content: "Integrable (fun p => p^2 * (Phi(u+p) * Phi(u-p))) for EVERY centre u"
  method: "explicit majorant, NOT Fubini: riemannXiKernel_le_majorant + evenness give Phi <= C globally; then p^2 Phi(u-p) is integrable via (u-q)^2 Phi(q) = u^2 Phi - 2u kM1 + kM2, reflected and translated"
  consequence: "C3B18.Rker_antitone_of_logConcave' : pointwise antitonicity whose ONLY hypothesis is about Phi"
piece_2_status:
  name: xiKernel_log_concaveOn
  status: OPEN
  numerics: "(log Phi)'' > 0 at 0 of 724 points on the FULL line (reflection for t<0), max -18.7269 at t=0; hazard nondecreasing (0 decreases); Phi Phi'' - (Phi')^2 < 0 everywhere sampled"
  exact_remaining_inequality: "the DIAGONAL surplus must dominate the OFF-DIAGONAL deficit in the compiled Finset split (C3B18.midpoint_nonneg_of_diag_dominates). Measured |OFF|/DIAG = 1.4e-2, 1.6e-5, 4.1e-13, 6.0e-40 at t = 0.1, 0.4, 0.8, 1.2."
  per_term_theorem_NOT_used_as_mixture: "cross-pair inequality violated 33/36; false in general for log-linear terms"
signed_lobe_unlocked:
  name: C3B18.lobe_block_antitone
  content: "consecutive half-period blocks of the clocked kernel have decreasing mass"
  method: "|cos(2xv)| has half period pi/(2x); Rker(v+pi/(2x)) <= Rker v by antitonicity; translation invariance of the interval integral"
  limitation_stated: "the FIRST block is half-length, so J0 >= J1 is NOT implied; batch 16 measured J0 - J1 < 0 for x >~ 8.86. The alternating-series assembly over infinitely many blocks is NOT formalised."
failed:
  - "F1 per-term log-concavity is not a mixture theorem: cross-pair violated 33/36"
  - "F2 TP2 of the mode kernel fails in the stated orientation, 9/9 (family is TP2 in the reversed mode order); does not give log-concavity of the sum either way"
  - "F3 Prekopa still absent from Mathlib and still unnecessary"
  - "F4 J0 >= J1 not delivered by the block lemma (first block half-length)"
  - "F5 Finset -> tsum needs double-series summability; midpoint -> ConcaveOn needs continuity of Phi on the whole line (repo has Ici 0 only)"
literature_check_still_required:
  - "first Laguerre inequality for the Riemann Xi function: NOT read at source (web tools unavailable, EIGHT sessions running). NO novelty claimed anywhere."
open_next_lean_statement: |
  theorem xiKernel_continuous : Continuous riemannXiKernel
open_next_purpose: "from riemannXiKernel_continuousOn (Ici 0) plus evenness, by gluing at 0. Required for ANY passage from midpoint log-concavity to ConcaveOn, and independent of the double-sum question so it can be landed separately. A prerequisite, NOT the main obstruction, which remains the diagonal-dominates inequality."
```
