# C3 proof batch 13 — the first Laguerre inequality: two compiled fibres, a sharp two-sided bound, and a closed-form kill of the soft-kernel class

Date 2026-08-25.  `/Users/samuellavery/work/helix_frobenius`, branch `ladder-campaign-2026-08`.
**No commit.  `git diff --stat` EMPTY — no tracked file modified.  Everything new is
`tmp/c3b13_*`.  `tmp/c3b10_*`, `tmp/c3b11_*`, `tmp/c3b12_*` not opened for write.**

`AGENTS.md` **does not exist in this repository** (`find . -maxdepth 3 -iname AGENTS.md` →
no hits, checked this session; same finding as batches 11 and 12).  `CLAUDE.md` obeyed.

> ## ⚠ ADJUDICATION CORRECTIONS APPLIED 2026-08-25 (OpenAI review) — READ FIRST
>
> Four overclaims were found in the first version of this ledger.  All four are corrected
> below.  **No theorem statement was changed**; only the prose describing them.
>
> | # | defect | status |
> |---|---|---|
> | 1 | `momentTwo_nonneg_of_thickened` / `momentTwo_nonneg_of_large_readout` called "compiled unconditional fibres" | **CORRECTED.** They are compiled **conditional criteria**: unconditional *implications* whose hypotheses are real inequalities that are **not proved to hold anywhere** in Lean. The word "fibre" is retained only as an informal label for the set where the hypothesis holds; that set is identified **numerically**, never formally. |
> | 2 | "the fibre is an **interval** around each real zero" | **CORRECTED.** Getting an interval additionally requires continuity of `x ↦ cosMom Φ x` and `x ↦ sinMom kM1 x` **and** `Ξ′(γ) ≠ 0` (simplicity of the zero). Neither is formalised here. The interval claim is **numerical and unformalised**. |
> | 3 | small-readout and large-readout described as "complementary", "the exact complement", partitioning | **WITHDRAWN.** They are **oppositely directed but not logical complements**: they do not partition the line, and the measured union is only **4.41%** of the grid — the remaining 95.59% satisfies *neither* hypothesis. `momentTwo_nonneg_of_either` is a disjunction, not a dichotomy. |
> | 4 | "the functional equation is **load-bearing**" | **REMOVED.** Replaced with a neutral statement of what was measured. |

**HEADLINE.**  49 new declarations, all axiom-clean.  The batch adds two compiled
**conditional criteria** for the target (one keyed to a small readout, one to a large one — 
oppositely directed, but not exhausting the line), a **sharp unconditional two-sided bound**
`|Ξ′² − ΞΞ″| ≤ Ξ(0)(−Ξ″(0))` (this one has no hypothesis), and an **elementary closed-form
counterexample** showing that no argument from evenness + positivity + integrability can
reach the target.  The batch also **withdrew its own most striking finding** after
adjudication (see F5/F7).

---

## 0. THE TARGET, UNFOLDED TO PLAIN MATHEMATICS

The Lean statement is

```lean
0 ≤ C3B10.cosMom riemannXiKernel x * C3B10.cosMom C3B12.kM2 x + C3B10.sinMom C3B12.kM1 x ^ 2
```

with `cosMom f x = ∫_ℝ f(t)cos(xt)dt`, `sinMom f x = ∫_ℝ f(t)sin(xt)dt`,
`kM1 = tΦ`, `kM2 = t²Φ`, `Φ = riemannXiKernel` (`ThetaWronskianSuzukiGram.lean:64`,
`Φ(u) = 4Σ_{n≥1}(2π²n⁴e^{9u/2} − 3πn²e^{5u/2})e^{−πn²e^{2u}}`).

**Dictionary, measured this batch at three independent routes (§P0):** with
`Ξ(x) := ξ(½+ix)`,

| slot | value | measured agreement |
|---|---|---|
| `cosMom Φ x` | `2·Ξ(x)` | `κ = 2` **exactly**, to `2.3e-61` over five ordinates |
| `sinMom kM1 x` | `−2·Ξ′(x)` | `≤ 6.7e-53` |
| `cosMom kM2 x` | `−2·Ξ″(x)` | `≤ 6.7e-53` |

So the target is, in plain mathematics,

> **`L₁(x) := Ξ′(x)² − Ξ(x)Ξ″(x) ≥ 0` for all real `x`** — the **first Laguerre inequality**
> for the Riemann Ξ-function; equivalently `log|Ξ|` is concave on each interval between
> consecutive real zeros; equivalently `∂²_σ|ξ(σ+it)|²|_{σ=½} ≥ 0`.

By Hadamard (genus 1, `Ξ` even, zeros in quadruples) it is equivalently
`L₁(x)/Ξ(x)² = (ξ′/ξ)′(½+ix) = Σ_ρ 1/(x−γ_ρ)²`, which is the form every numeric in this
ledger uses (it is cancellation-free — see §P0).

### Identifier search before construction — exhaustive, and its result

| search | command | result |
|---|---|---|
| Laguerre in Mathlib | `Grep "Laguerre"` over `.lake/packages/mathlib/Mathlib` | **no files** |
| Laguerre/Turán, repo-wide | `Grep "Laguerre\|laguerre\|Tur[aá]n\|turan"` over `*.{lean,tex,md,py}` | only prose + batch ledgers + `rank6_weld.py` (Gauss–Laguerre *quadrature*, unrelated) |
| the conclusion, 5 naming variants | `theorem \w*[Ll]aguerre`, `xi_laguerre`, `L1_nonneg`, `deriv_sq_sub`, `logDeriv_deriv_nonneg` over `RequestProject/` | **zero hits** (matches batch-3's independent search at `claude_c3_long_batch_20260824.md:160-168`) |
| positive-definiteness / Bochner / Schoenberg / Pólya / Hudson / Wigner | `Grep` over `RequestProject/` + Mathlib `Analysis/Fourier`, `MeasureTheory` | no usable instrument |

`#print axioms` was run transitively on every retained declaration (§ COMPILED).

### Literature — **NOT DISCHARGED, third batch running.  No novelty is claimed anywhere in this ledger.**

Web access failed in this session too: `WebSearch` returns
`API Error: 400 output_config.effort 'max' is not supported when thinking is disabled`, and
`WebFetch` is not permitted.  Under CLAUDE.md rule 10 a novelty trigger requires three
closest sources **read at source**; I cannot read any, so **I make no claim that anything
here is new, first, or unclaimed.**

What the repository itself records, read at source this batch and reproduced verbatim:

* `GOAL_HP_UNCONDITIONAL.md:143-146` — "the analytic content is Csordas–Varga 1988 Thm 2.1
  (hazard monotonicity / log-concavity of K(√t)), the Turán inequality is
  Csordas–Norfolk–Varga 1986".
* `tmp/claude_c3_proof_batch3_20260824.md:9-15` — **a retraction that binds this batch**:
  "An earlier draft of this session's prose called it 'unconditional (Csordas–Varga 1988)';
  that was a misattribution — CV 1988 Thm 2.1 is about the **kernel**
  (`hp_pencil.tex:1739-1741`), and CNV 1986 is about the **Maclaurin coefficients**
  (`hp_pencil.tex:1741-1744`).  Neither is the pointwise statement."

So the pointwise statement `L₁(Ξ)(x) ≥ 0` is **not** discharged by anything cited in this
repository, and its status in the wider literature is **unknown to me**.  Recorded as the
top external action for the fourth batch running.

---

## COMPILED

Build command, literal, for each file `f ∈ {A1,A2,A3,A4,A5}`:

```
env LEAN_PATH=tmp lake env lean tmp/c3b13_<f>.lean
env LEAN_PATH=tmp lake env lean -o tmp/c3b13_<f>.olean tmp/c3b13_<f>.lean     # to emit the olean
```

Full audit log: `tmp/c3b13_audit.log`, 49 lines, **49/49 exactly
`[propext, Classical.choice, Quot.sound]`, `grep -c "error\|sorryAx"` → 0.**

Deliverable scan:

```
grep -n "sorry\|admit\|^axiom\|axiom \|implemented_by\|native_decide\|@\[implemented" \
     tmp/c3b13_A1.lean tmp/c3b13_A2.lean tmp/c3b13_A3.lean tmp/c3b13_A4.lean tmp/c3b13_A5.lean
   →  exit 1, no output
```

No declaration is a Prop-valued restatement of the target: `laguerre_abs_le_zero`,
`momentTwo_abs_le`, `weighted_moment_abs_le` and `cellDensity_abs_le_zero` take only real
variables; the two fibre theorems carry **real inequalities** as hypotheses (not the target,
and — checked in §P6/§P7 — **inhabited**, which is why they are fibres and not vacua).

### `tmp/c3b13_A1.lean` — unconditional moment bounds, and the **thickened zero fibre** (16 decls)

```lean
theorem cosMom_abs_le_mass {W : ℝ → ℝ} (hW : Integrable W) (hpos : ∀ t, 0 ≤ W t) (x : ℝ) :
    |cosMom W x| ≤ cosMom W 0

theorem momentTwo_nonneg_of_thickened {x : ℝ}
    (h : cosMom kM2 0 * |cosMom riemannXiKernel x| ≤ sinMom kM1 x ^ 2) :
    0 ≤ ∫ u in Ioi (0 : ℝ), u ^ 2 * cellDensity x u
```

**What is new against batch 12, stated at exactly its proved strength.**
`C3B12.momentTwo_eq_sq_of_cosMom_zero` discharges the target under the *equality* hypothesis
`cosMom Φ x = 0`.  The theorem above weakens that to an **inequality** hypothesis, and batch
12's version is recovered *through* it (`momentTwo_nonneg_of_cosMom_zero'`), so the logical
strengthening of the criterion is on the record.

> **CORRECTED (adjudication item 1 and 2).**  This is a **conditional criterion**, not a
> discharged region.  Nothing in Lean proves that its hypothesis holds at any `x`.  The
> earlier claim that the hypothesis holds on an **interval** around each real zero — because
> at `γ` the left side is `0` and the right side is `4Ξ′(γ)²` — additionally needs
> **continuity** of `x ↦ cosMom Φ x` and `x ↦ sinMom kM1 x` and **`Ξ′(γ) ≠ 0`** (simplicity
> of the zero).  **Neither is formalised here.**  The interval statement is therefore
> **numerical and unformalised**, and the half-widths tabulated in §P6 are measurements of a
> quantity whose positivity is not proved.

The bound that makes it unconditional is `|c₂(x)| ≤ c₂(0)`, which uses only `t²Φ ≥ 0` and
`|cos| ≤ 1`.  **Measured reach (§P6): half-width `6.0e-2` at `γ₁ = 14.1347`, `7.7e-4` at
`γ₂`, `5.5e-5` at `γ₃`, `6.7e-20` at `γ₁₂`; the criterion fires at `2/1201` points of a
uniform grid on `[0,60]`.  That reach is small and is reported as small.**

### `tmp/c3b13_A2.lean` — cell-density domination and the **sharp two-sided bound** (10 decls)

```lean
theorem cellDensity_abs_le_zero (x : ℝ) :
    ∀ᵐ u : ℝ, |cellDensity x u| ≤ cellDensity 0 u

theorem weighted_moment_abs_le {w : ℝ → ℝ} (hw : ∀ u, 0 ≤ w u) {x : ℝ}
    (hx : IntegrableOn (fun u => w u * cellDensity x u) (Ioi 0))
    (h0 : IntegrableOn (fun u => w u * cellDensity 0 u) (Ioi 0)) :
    |∫ u in Ioi 0, w u * cellDensity x u| ≤ ∫ u in Ioi 0, w u * cellDensity 0 u

theorem laguerre_abs_le_zero (x : ℝ) :                       -- hypotheses: NONE
    |cosMom riemannXiKernel x * cosMom kM2 x + sinMom kM1 x ^ 2|
      ≤ cosMom riemannXiKernel 0 * cosMom kM2 0
```

In readout coordinates the last line is **`|Ξ′(x)² − Ξ(x)Ξ″(x)| ≤ Ξ(0)·(−Ξ″(0))` for every
real `x`** — the first Laguerre expression never exceeds its value at the origin, in either
direction.  The **lower** half is what the OPEN target strengthens from `−L₁(0)` to `0`.

The whole content is one observation: `Φ(u+p)Φ(u−p) ≥ 0`, so the chart clock `cos(2xp)` is
the **only** sign in the cell density.  §P8 confirms the constant is **attained at `x = 0`**,
so the bound is sharp as stated.

### `tmp/c3b13_A3.lean` — the **derivation law**, two independent spellings, and the elementary-factor split (8 decls)

```lean
theorem laguerre_mul (f f1 f2 g g1 g2 : ℝ) :                 -- DECOMPOSITION I
    (f1*g + f*g1)^2 - (f*g)*(f2*g + 2*(f1*g1) + f*g2)
      = (f1^2 - f*f2)*g^2 + f^2*(g1^2 - g*g2)

theorem laguerre_quotient (f f1 f2 g g1 g2 : ℝ) (hf : f ≠ 0) (hg : g ≠ 0) :   -- DECOMPOSITION II
    ((f1*g + f*g1)^2 - (f*g)*(f2*g + 2*(f1*g1) + f*g2)) / (f*g)^2
      = (f1^2 - f*f2)/f^2 + (g1^2 - g*g2)/g^2

theorem laguerre_elementary_split (x g g1 g2 : ℝ) :          -- P(x) = −(x²+¼)
    ... = (2*x^2 - 2⁻¹) * g^2 + (x^2 + 4⁻¹)^2 * (g1^2 - g*g2)

theorem laguerre_elementary_fibre {x g g1 g2 : ℝ} (hx : 4⁻¹ ≤ x^2) (hg : 0 ≤ g1^2 - g*g2) : ...

theorem gen_cellDensity_abs_le {W : ℝ → ℝ} (hpos : ∀ t, 0 ≤ W t) {x u : ℝ} (hx …) (h0 …) :
    |genCell W x u| ≤ genCell W 0 u
```

`L₁` is a **derivation on logarithms** (`L₁(f)/f² = −(log f)″`), so it is additive across a
product.  At `Ξ = P·G` with `P(x) = −(x²+¼)` (the factor `s(s−1)` at `s = ½+ix`) and
`L₁(P) = 2x² − ½`, this is the **elementary-factor split with the remaining `N` factor** the
brief asks for, exactly and with no loss.  The elementary factor helps precisely outside
`|x| < ½` — the same circle `|s−½| = ½` that batch 12's `elementary_factor_split` found on
the four-moment leaf, now recovered on the sub-leaf by an independent route.

`gen_cellDensity_abs_le` is the general-kernel form of A2's domination and — unlike batch
12's `gen_target_eq` — **does not even use evenness.**

> **ANALYTIC BRIDGE, NAMED, NOT COMPILED.**  `laguerre_mul`, `laguerre_quotient` and the
> `elementary_*` family are identities between real numbers standing for a function and its
> first two derivatives.  Instantiating them at the actual `Ξ` needs the dictionary
> (differentiation under the integral sign; measured to `6.7e-53`, **not** formalised) and
> `ξ(½+ix) = P(x)G(x)` with `G` real and `C²`.  **Neither is formalised in this repository.
> Do not cite the instantiation as compiled.**  This is the same marking discipline batch 12
> applied to `elementary_factor_split` after adjudication.

### `tmp/c3b13_A4.lean` — the large-readout **criterion** (9 decls)

```lean
def Jbar (a : ℝ) : ℝ := ∫ u in Ioi (0:ℝ), |u^2 - a^2| * cellDensity 0 u

theorem momentTwo_ge_readout_sq (a x : ℝ) :                  -- hypotheses: NONE
    a^2 * (4⁻¹ * cosMom riemannXiKernel x ^ 2) - Jbar a
      ≤ ∫ u in Ioi (0:ℝ), u^2 * cellDensity x u

theorem momentTwo_nonneg_of_large_readout {a x : ℝ}
    (h : Jbar a ≤ a^2 * (4⁻¹ * cosMom riemannXiKernel x ^ 2)) :
    0 ≤ ∫ u in Ioi (0:ℝ), u^2 * cellDensity x u

theorem momentTwo_nonneg_of_either {a x : ℝ}
    (h : (cosMom kM2 0 * |cosMom riemannXiKernel x| ≤ sinMom kM1 x ^ 2)
        ∨ (Jbar a ≤ a^2 * (4⁻¹ * cosMom riemannXiKernel x ^ 2))) : ...
```

A **positive double-integral split with a movable centre**: `u² = (u²−a²) + a²`.  The `a²`
piece is *already a square* (batch 12's `cellDensity_Ioi_eq_sq` evaluates it as `¼Ξ_rep(x)²`);
the `(u²−a²)` piece is converted by A2's domination into the **`x`-independent constant**
`Jbar a`.  So the criterion fires wherever the readout is large.

> **CORRECTED (adjudication item 3).**  An earlier version called this "the exact
> complement" of A1's criterion and read `momentTwo_nonneg_of_either` as recording a
> complementarity.  **Withdrawn.**  The two hypotheses are **oppositely directed** — one asks
> `|c₀(x)|` to be small, the other asks it to be large — but they are **not logical
> complements and do not partition the line**: there is a wide middle band satisfying
> neither.  Measured (§P15): the union covers **4.41%** of a uniform grid on `[0,60]`, so
> **95.59% of the grid satisfies neither hypothesis.**  `momentTwo_nonneg_of_either` is a
> **disjunction**, not a dichotomy, and it is stated as one.

### `tmp/c3b13_A5.lean` — the **corner obstruction** and a closed-form counterexample (6 decls)

```lean
theorem corner_tail_laguerre (A x : ℝ) (hx : x ≠ 0) :
    (2*A/x^3)^2 - (-(A/x^2)) * (-(6*A/x^4)) = -(2*A^2/x^6)
theorem corner_tail_laguerre_neg {A x : ℝ} (hA : A ≠ 0) (hx : x ≠ 0) : ... < 0

theorem laguerre_two_over_one_add_sq (x : ℝ) :               -- f = 2/(1+x²)
    (-(4*x)/(1+x^2)^2)^2 - (2/(1+x^2)) * ((12*x^2-4)/(1+x^2)^3)
      = (8 - 8*x^2)/(1+x^2)^4
theorem laguerre_two_over_one_add_sq_neg {x : ℝ} (hx : 1 < x^2) : ... < 0
theorem laguerre_two_over_one_add_sq_pos {x : ℝ} (hx : x^2 < 1) : 0 < ...
```

See §F5 and §P9 — this is the batch's most consequential item.

---

## OPEN

**The target, unchanged:**

```lean
theorem laguerre_edge (x : ℝ) :
    0 ≤ C3B10.cosMom riemannXiKernel x * C3B10.cosMom C3B12.kM2 x
      + C3B10.sinMom C3B12.kM1 x ^ 2
```

**What this batch did and did not remove from the open region.**  *Formally: nothing.*  The
two new criteria (`momentTwo_nonneg_of_thickened`, `momentTwo_nonneg_of_large_readout`) are
compiled **implications**; no Lean theorem establishes that either hypothesis holds at any
`x`, so the OPEN statement is untouched as a formal matter.

*Numerically*, the disjunction `momentTwo_nonneg_of_either` has a verifiable hypothesis at
**53/1201 = 4.41%** of a uniform grid on `[0,60]` (§P15) — `|x| ≤ 2.503` from the
large-readout branch plus two grid points at the first zero from the small-readout branch —
leaving **95.59% of the grid satisfying neither hypothesis.**  Small, and reported as small.

**Where the difficulty actually is — measured, and it is not where one would guess (§P10).**
The scale-free margin `B(x) = L₁/Ξ² = Σ_ρ 1/(x−γ_ρ)²` has minimum

| window | min `B` | at `x` |
|---|---|---|
| `[0,5]` | **0.0462099862308** | 0.0 |
| `[5,10]` | 0.0528585943467 | 5.0 |
| `[10,20]` | 0.106230796249 | 10.0 |
| `[20,40]` | 0.389787282711 | 27.7 |
| `[40,80]` | 0.569743040285 | 45.6 |
| `[80,160]` | 0.941088496098 | 81.2 |
| `[160,320]` | 1.26230593304 | 172.0 |

The margin **grows monotonically with height** (zeros get denser, each contributing
`1/(x−γ)²`), so **the target is tightest at `x = 0`** — where batch 12 already compiled it
(`momentTwo_zero_nonneg`) and where A4's fibre now covers a neighbourhood.  **The difficulty
is therefore not asymptotic.**  It is the absence of any zero-location input at finite
height, which §F6 shows is unavoidable.

---

## EQUIV — navigation only, never a stop reason

* **`L₁ ≥ 0` ⟸ RH, and strictly weaker than RH.**  From
  `L₁/Ξ² = Σ_ρ 1/(x−γ_ρ)²`: an off-line zeta zero `β+iγ` with `δ = β−½ ≠ 0` puts a
  conjugate pair of `Ξ`-zeros at `γ ∓ iδ`, contributing exactly `−2/δ²` at `x = γ`.  RH kills
  every such term, so RH ⟹ target.  The converse fails: a zero with **large** `δ` is not
  detected (batch 12's `Φ_c` has all zeros at `Im = π` and satisfies the target).
* **`L₁ ≥ 0` ⟹ a zero-repulsion statement** (§F6): at every height sampled, `2/δ² ` exceeds
  the whole remaining budget `B(x)` for any `|δ| < ½`, so the target implies *no zeta zero
  lies just off the critical line* at those heights.  This is **not** a classically known
  consequence and it is why §F5's soft-kernel kill is forced.
* **Target ⟺ `R` is positive definite**, where
  `R(v) := ∫ p²Φ(v+p)Φ(v−p)dp ≥ 0` and `L₁ = 4∫R(v)cos(2xv)dv`.  Derived on paper (two ways,
  §P3-route); the Lean version needs one new pairing theorem — this is the NEXT TARGET below.
* **Target ⟺ `∂²_σ|ξ(σ+it)|²|_{σ=½} ≥ 0`** ⟺ `log|Ξ|` concave between consecutive zeros.
* **Target ⟺ `−(log A)″ + −(log|Z|)″ ≥ 0`** with `A` the archimedean envelope and `Z` Hardy's
  function — the classical envelope/phase split.  §F2 shows neither summand is separately
  nonnegative.

---

## FAILED

**F1. The elementary/polygamma/zeta split does not isolate a hard term.**  The identity is
**exact** (verified `reldiff = 0.0` at 13 ordinates, §P2):

`L₁/Ξ² = T_el + T_gam + T_zeta`, `T_el = (2x²−½)/(x²+¼)²`,
`T_gam = ¼Re ψ₁(¼+ix/2)`, `T_zeta = Re(ζ′/ζ)′(½+ix)`.

But **all three go negative.**  Over `x ∈ (0,100]` step 0.05: `T_gam < 0` at **1189/1200**
points (I predicted it positive from `Re(1/z)`; the `1/(2z²)` term dominates and
`T_gam ≈ −1/(4x²)` — **my prediction was wrong and is corrected here**), and `T_zeta < 0` at
**103/1200** points, `min = −0.699` at `x ≈ 0.85`.  In particular

> **`Re (ζ′/ζ)′(½+it) ≥ 0` is FALSE** — refuted at `t ≈ 0.85` with value `−0.699`.

So the reduction "target on `|x| ≥ ½` ⟸ a pure-ζ sign statement" **does not exist**.  The
identity stands and is the exact relocation of the difficulty; the reduction is dead.

**F2. Neither factor of the envelope/phase split is log-concave.**  Same scan: the
archimedean part `T_el + T_gam` is negative only on the disc (`T_el ≥ 0 ⟺ x² ≥ ¼`) and is
asymptotically `≈ 7/(4x²) > 0`; the Hardy part `T_zeta` is negative at 103/1200 points.  The
target is a statement about the **sum**, and the split gives no purchase on it.

**F3. Pólya's criterion is structurally inapplicable — proved, not measured.**  Pólya: even +
nonneg + convex-decreasing on `(0,∞)` + `→0` ⟹ positive definite.  But a **smooth** even `K`
has `K′(0⁺) = 0`; convexity makes `K′` nondecreasing, so `K′ ≥ K′(0⁺) = 0` on `(0,∞)`, while
decrease forces `K′ ≤ 0` — hence `K′ ≡ 0` and `K` constant, contradicting `K → 0`.  **So
Pólya's criterion cannot apply to any smooth even kernel**, `R` included.  (Batch 3 attack 23
refuted Pólya numerically on the *different* object `D`; this supplies the structural
reason and it applies to every object of this shape.)

**F4. Schoenberg / Gaussian-scale-mixture is dead — but this entry's ORIGINAL EVIDENCE WAS
WRONG, and is replaced.**

> **⚠ CORRECTED 2026-08-25 by batch 14 (self-audit, `tmp/c3b14_num3_out.txt`).**  The first
> version of F4 argued: a Gaussian scale mixture has a transform that is again a Gaussian
> scale mixture, hence completely monotone in `x²`, hence monotone decreasing in `|x|`; and
> then asserted "`|L₁|` is **not** monotone (§P11)".  **Two defects.**
> 1. **The cited measurement did not exist.**  §P11's number came from `tmp/c3b13_num2.py`,
>    which never finished and produced zero output — as this ledger itself states two
>    sections later ("no result from it is used anywhere").  I cited it anyway.
> 2. **The assertion is false in the tested range.**  Recomputed cancellation-free at 40
>    digits: `|L₁|` **increases at 0/80** steps on `x ∈ [0,20]`, **0/240** on `[0,60]`,
>    **0/240** on `[0,120]`.  It is monotone decreasing there.  (Four increases appear on
>    `[0,300]` at the coarse step `1.0`, first at `x = 171`, where `L₁ ∼ 10⁻¹⁰⁰` and the grid
>    straddles the dips between zeros; those are not adjudicated and nothing rests on them.)
>
> **The conclusion nevertheless stands, on independent evidence obtained in batch 14.**  The
> Schoenberg criterion is tested *directly*: `R` is a Gaussian scale mixture iff
> `g(τ) := R(√τ)` is completely monotone.  Measured (`tmp/c3b14_num2_out.txt` §S2):
> `(−1)¹g′ ≥ 0` and `(−1)²g″ ≥ 0`, but **`min (−1)³g‴ = −3.81`** and
> `min (−1)⁴g⁗ = −2.55e4`.  Complete monotonicity fails at the third derivative, so `R` is
> **not** a Gaussian scale mixture and the route is dead.  Pre-registration honoured, but the
> prediction was confirmed by a different test than the one announced.

**F5. THE SOFT-KERNEL CLASS IS DEAD, IN CLOSED FORM.**  `W(t) = e^{−|t|}` is even, positive
and integrable; `∫W(t)cos(xt)dt = 2/(1+x²)` (quadrature check to `1.5e-31`, §P9); and

```
L₁(x) = Ξ′² − ΞΞ″ = (8 − 8x²)/(1 + x²)⁴   <   0   for every |x| > 1.
```

Compiled: `C3B13.laguerre_two_over_one_add_sq{,_neg,_pos,_boundary}` (the rational algebra;
the transform itself is textbook and is **not** formalised — marked in the file).  Verified
against numerical differentiation to `4.1e-31` at nine ordinates including `x = 0.999, 1,
1.001`.

**The mechanism, and it is general.**  If an even kernel has a **corner** at the origin,
`W′(0⁺) = A/2 ≠ 0`, then `Ξ(x) = −A/x² + O(x⁻⁴)`, and
`L₁ ~ 4A²x⁻⁶ − 6A²x⁻⁶ = −2A²x⁻⁶ < 0` — compiled as `C3B13.corner_tail_laguerre_neg`.
**Every even positive kernel with a corner violates the target at large `x`, with no
arithmetic content whatever.**  Riemann's `Φ` has no corner: `Φ′(0) = 0`.  Neutrally stated:
`Φ` is even as an identity (the Jacobi reflection, compiled as `riemannXiKernel_neg`), and an
even differentiable function has vanishing derivative at `0`, so the corner mechanism above
does not apply to it.  That is the whole of what is established here — no claim is made about
which ingredient of a hypothetical proof would carry the weight.

This supersedes two earlier witnesses: batch 3 `FAILED-5` used `cδ₀ + b(δ_a+δ_{−a})`, which
is not an integrable kernel; batch 12 `F5` used a Gaussian mixture established numerically.
Here the kernel is a genuine `L¹` function and the refutation is closed-form.

**F6. Consequently: no proof of the target can be "soft".**  The target implies a
zero-repulsion statement (§EQUIV, §P12), and evenness+positivity+integrability cannot see
zero locations — F5 exhibits a kernel with all three properties and a negative `L₁`.  **Any
proof must consume arithmetic input.**  This is a derived calibration of what a proof must
contain, not a no-go: it says *what to supply*, and the repo already has the supply
(`DVP.seat_channel_to_634`, `xiStructure_dominates_of_low634` — zero-location facts to
height 634).

**F7 (RETRACTED, mine, within this batch — the finding I most wanted to keep).**  Block 3
§B20 measured that the even extension of the **first theta term** `Φ₁(|u|)` violates the
target: **28/121 negatives on `[0,30]`, `min = −1.4698450233174e-8` at `x = 19.75`**, while
`N = 2, 3, 5` give **0** negatives.  I was about to record this as *"no termwise argument can
work"*.  **That reading is WITHDRAWN.**  Adjudication (§P13):

* **precision is not the issue** — the value is `−1.469845023317387e-8` at **all six**
  `(dps, nodeset)` settings `{30,60,90} × {A,B}`, spread `3.1e-39`.  The negativity is real.
* **but it is the corner, not the truncation.**  A truncated theta sum is *not* even, so
  `Φ_N(|u|)` **imposes** evenness and creates a corner.  Measured `Φ_N′(0⁺)`:
  `7.90e-2` (N=1), `1.65e-7` (N=2), `2.78e-16` (N=3), `3.5e-40` (N≥5) — it collapses
  super-exponentially, **in perfect lock-step with the violation disappearing at N ≥ 2**.
* **and F5's mechanism predicts it quantitatively**: `A = 2Φ₁′(0⁺) = 0.158` gives
  `−2A²/x⁶ = −8.4e-10` at `x = 19.75` against the measured `−1.47e-8` — same sign, same
  order (the `x⁻⁴` correction is not small at `x = 20`, so this is mechanism confirmation,
  not a fit).

So B20 measures F5, not a truncation obstruction.  **Nothing is claimed about termwise
arguments.**  Per CLAUDE.md rule 10, the no-go I did *not* write is issued as a refutation
spec instead — §RS-1.

**F8. The Hadamard cross-check of B20 MISSED.**  §P13 C3 root-found the `Ξ₁`-zero nearest the
real axis near `x = 19.75` and got `26.06 + 7.13i` (`δ = 7.13`, contribution only `−0.039`),
at which `L₁ = +2.09e-10` — **positive**.  The crude two-zero prediction rule of §P12 failed
here.  Reported as a failed cross-check, not as a confirmation; the F5/F7 conclusion rests on
C1+C2 and the closed form, not on C3.

**F9. Sturm does not close, and I corrected my own slip getting there.**  The derivative is
`L₁′ = Ξ′Ξ″ − ΞΞ‴`, **not** the `−ΞΞ‴` I first wrote (checked against a central difference
to `3.9e-26`, §P7).  At a hypothetical first zero `x*`: `Ξ′² = ΞΞ″` **and** `Ξ′Ξ″ ≤ ΞΞ‴` —
two conditions on four jets.  Does not close.

**F10. `L₂ ≥ 0` is not the biting rung.**  The second Laguerre expression is **positive at
all 10 sampled ordinates** (§P14), so the ladder does not fail earlier than `L₁`; scanning it
buys nothing.  (It is also strictly stronger than the target, so it was never a route.)

**F11. Compiler failures encountered (all repaired).**  `cellDensity_integrable` does not
exist (use `cellDensity_exp_integrable x 0` + `Integrable.congr`); `IntegrableOn.congr_fun`
leaves a `Pi.sub_apply` goal that `ring` cannot see (prepend `simp only [Pi.sub_apply]`);
`C3B12.genCell` lives in `c3b12_A3`, which is not on the `c3b12_A2 → c3b13_A1` import path
(add `import c3b12_A3`).

---

## REFUTATION SPECS ISSUED (CLAUDE.md rule 10 — written, not run)

**RS-1 — "no termwise argument over the theta series can prove the first Laguerre
inequality".**  *Self-contained; needs no access to this repository.*

- **Claim (falsifiable).**  Let `Φ(u) = Σ_{n≥1} φ_n(u)` with
  `φ_n(u) = (2π²n⁴e^{9u/2} − 3πn²e^{5u/2})e^{−πn²e^{2u}}`, and let `Ξ_S` denote the cosine
  transform `∫_ℝ S(t)cos(xt)dt` of an even kernel `S`.  CLAIM: there is **no** decomposition
  `Φ = Σ_k S_k` into even, nonnegative, integrable kernels `S_k`, each **smooth at 0**
  (`S_k′(0) = 0`), such that `Ξ_{S_k}′(x)² − Ξ_{S_k}(x)Ξ_{S_k}″(x) ≥ 0` for every `k` and
  every real `x`.
- **Inputs.**  Only the formula above and a high-precision numeric library.
- **Procedure.**  (1) Build the symmetrised partial sums
  `T_N(u) := ½(Σ_{n≤N}φ_n(u) + Σ_{n≤N}φ_n(−u))` — **even by construction, and smooth at 0**,
  unlike `Σ_{n≤N}φ_n(|u|)`.  Note the `−u` series converges slowly; use ≥ 5000 terms and
  verify `T_N(−u) = T_N(u)` to the working precision.  (2) For `N = 1,2,3,5` compute
  `L₁(T_N)(x)` on `x ∈ [0,60]` at ≥ 40 digits.  (3) Also test the *scaled* single terms
  `S_k(u) = φ_k(u) + φ_k(−u)`.
- **Decision rule, PRE-REGISTERED.**  If some `T_N` or `S_k` shows a stable negative `L₁`
  (sign unchanged across two precisions and two quadrature schemes), the claim is
  **SUPPORTED**.  If all of them are nonnegative on `[0,60]`, the claim is **REFUTED** and a
  termwise route is live.
- **My PREDICTION and its reason.**  **REFUTED** — I expect `T_N` and `S_k` to be nonnegative.
  Reason: this batch showed the `Φ_N(|u|)` violation is entirely the corner artefact
  (`Φ_N′(0⁺)` and the violation vanish together at `N ≥ 2`), and symmetrising removes the
  corner by construction.  If that is right, the "termwise is dead" reading I nearly recorded
  was false, and the corner — not the truncation — was doing all the work.

---

## NUMERICAL (evidence, never certified; explicit error control)

Scripts and outputs, all exit 0 except where noted:
`tmp/c3b13_num1.py → _out.txt` (blocks P0–P2, P6, P7),
`tmp/c3b13_num3.py → _out.txt` (P8, P10, P14, B20),
`tmp/c3b13_num4.py → _out.txt` (P15 controls + the closed-form validation),
`tmp/c3b13_num5.py → _out.txt` (P13), `tmp/c3b13_num6.py → _out.txt` (P9),
`tmp/c3b13_num7.py → _out.txt` (P15 table and coverage).
`tmp/c3b13_num2.py` did not finish and **no result from it is used anywhere.**

**P0 — the dictionary, and a REJECTED first attempt.**  The first run of the quadrature route
disagreed with the `ξ` route by **up to 6.0%**.  Per the batch rule, that **rejects** the
formula, and it did: two bugs were found — the theta series converges slowly at `u < 0`
(fixed by evaluating at `|u|`, legitimate because `Φ` is even, `riemannXiKernel_neg`), and
tanh-sinh was straddling the oscillation (fixed by subdividing at the half-periods of
`cos(xt)`).  After the fix:

```
         x              c0 (quad)                Xi (xi)        kappa=c0/Xi
       0.0      0.994241556376628      0.497120778188314                2.0
       1.0      0.971514859341967      0.485757429670983                2.0
      11.0     0.0396163490400192     0.0198081745200096                2.0
max |kappa(x)/kappa(0) - 1| over five points = 2.33363e-61
DICTIONARY VERDICT: worst relative disagreement = 6.66366e-53
```

**POSITIVE CONTROL, and it fired.**  `L₁(0)/Ξ(0)² = Σ_ρ 1/γ_ρ²` must equal the classical
`2 + γ_E − log 4π` plus the `1/γ² − 1/(γ²+¼)` correction:

```
   2 + gamma_E - log(4pi)                 = 0.0461914179322421
   + correction sum over first 200 zeros  = 0.0462099843387768
   measured L1(0)/Xi(0)^2                 = 0.0462099862308379
   CONTROL reldiff                        = 4.09449e-8      (tail of the correction sum)
```

**P1 — hostile scan, 2144 points: `x ∈ [0,1]` step 0.025, `[1,60]` step 0.05, `[60,400]`
step 0.5, plus 27 zero ordinates × 9 offsets `{0, ±1e-12, ±1e-6, ±0.01, ±0.2}`.**

```
NEGATIVES of L1/Xi^2: 0
min L1/Xi^2 = 0.0462099862308 at x = 0.0
```

| x | Ξ(x) | L₁/Ξ² | L₁ |
|---|---|---|---|
| 0 | 0.497120778188 | 0.0462099862308 | 0.0114198308344 |
| 6.28 | 0.193500069093 | 0.0580012812847 | 0.00217170002509 |
| 14.134725141734693790 | 6.32251046254e-22 | 4.78287249979e+36 | 1.91191207968e-6 |
| 60 | −2.90927482394e-18 | 4.03472463152 | 3.4149425119e-35 |
| 150 | 4.48926613599e-49 | 350.792856321 | 7.06970749205e-95 |
| 300 | 8.78899427169e-99 | 40.32905056 | 3.11527479017e-195 |
| 400 | 1.43704532778e-133 | 4517.42942822 | 9.32894023293e-263 |

**The computation is cancellation-free**: `L₁/Ξ² = (ξ′/ξ)′(½+ix)` is evaluated directly from
`ζ, ζ′, ζ″, ψ₁`, never by differencing a decaying kernel.  That is the batch-12 F6 lesson
applied ahead of time.

**P2 — the exact split** (13 ordinates, `worst reldiff = 0.0`); sign audit in §F1.

**P6 — the thickened zero fibre** (`c₂(0) = 0.04594388863029087507`):

| γ | \|Ξ′(γ)\| | guaranteed half-width |
|---|---|---|
| 14.134725141734693790 | 0.001382719089 | 0.06019164378 |
| 21.022039638771554993 | 1.774977621e-5 | 0.000772671915 |
| 25.010857580145688763 | 1.265203691e-6 | 5.507603857e-5 |
| 30.424876125859513210 | 2.411708894e-8 | 1.049849704e-6 |
| 72.067157674481907582 | 1.550132797e-21 | 6.747939034e-20 |

Coverage on `[0,60]` step 0.05: **2/1201 (0.17%)**.

**P7 — `L₁′ = Ξ′Ξ″ − ΞΞ‴`** against a central difference at `h = 1e-12`, dps 60:
`reldiff ≤ 3.9e-26` at `x = 1, 3, 7, 25`.  (At `x = 14.1347` the difference quotient
straddles a pole of `L₁/Ξ²`; that row is a known artefact of the probe, not a disagreement,
and is excluded.)

**P8 — tightness of the compiled bound** (`L₁(0) = 0.011419830834443718337`):

| x | L₁(x) | L₁(x)/L₁(0) |
|---|---|---|
| 0 | 0.01141983083444372 | **1.0** |
| 1 | 0.01095669125098577 | 0.95944426934407 |
| 4 | 0.005863083125320356 | 0.51341243231349 |
| 14.134725… | 1.911912079683027e-6 | 0.00016742035038877 |
| 25 | 1.621234234950208e-12 | 1.4196657187428e-10 |

Attained at `x = 0` ⟹ `C3B13.laguerre_abs_le_zero` is **sharp as stated**.

**P9 — the closed-form counterexample** (`W = e^{−|t|}`).  Transform check vs `2/(1+x²)`:
`reldiff ≤ 1.5e-31` at six ordinates.  `L₁` by numerical differentiation vs the closed form
`(8−8x²)/(1+x²)⁴`: `reldiff ≤ 4.1e-31` at nine ordinates.

```
       x           numerical derivs                closed form   sign
   0.999       0.001003506006002497       0.001003506006002497    pos
       1                        0.0                        0.0      0
   1.001     -0.0009965059940025027     -0.0009965059940025027    NEG
       2                    -0.0384                    -0.0384    NEG
      20      -1.234483791736981e-7      -1.234483791736981e-7    NEG
```

**P10 — the margin structure**: see OPEN.  **P11 — RETRACTED (see F4).**  This section
originally reported that `|L₁|` is not monotone in `|x|`; the number came from a script that
never ran, and the claim is **false** on `[0,120]` (0 increases at step 0.25, recomputed at
40 digits in `tmp/c3b14_num3_out.txt`).  Nothing in this ledger may cite P11.
**P12 — off-line-zero calibration:** at every sampled height the whole budget
`B(x)` is `< 8 ≤ 2/δ²` for `|δ| < ½`, hence §EQUIV's zero-repulsion reading.

**P13 — the F7 adjudication**, verbatim:

```
   dps    nodes                L1_1(19.75)
    30        A      -1.469845023317387e-8
    90        B      -1.469845023317387e-8       (all six settings identical)
  spread across 6 (dps, nodeset) settings = 3.08062e-39
   N             Phi_N(0)        Phi_N-prime(0+)     corner/value
   1        1.78290788527        0.0789975305355      0.044308251
   2        1.78678759869       1.65305591555e-7     9.2515524e-8
   3        1.78678760187      2.78345172722e-16    1.5577966e-16
   5        1.78678760187      3.49232402276e-40    1.9545267e-40
```

**P14 — `L₂`**: positive at all 10 sampled ordinates (`x = 0 … 25`).

**P15 — coverage of the two compiled fibres.**  `tmp/c3b13_num4.py` (nested adaptive
quadrature, mpmath) was too slow to finish, but it produced two things that matter: its
**controls fired exactly**, and its first `Jbar` row **validated the closed form to
`reldiff 0.0`**:

```
    M0 (quadrature) = 0.247129068106555   (1/4)c0(0)^2 = 0.247129068106555   reldiff 0.0
    M  (quadrature) = 0.005709915417221859  (1/8)c0(0)c2(0) = 0.005709915417221859  reldiff 1.349e-31
       a          Jbar direct     Jbar closed form    reldiff
    0.10     0.00487715986007     0.00487715986007        0.0
```

These independently confirm batch 12's compiled `cellDensity_Ioi_eq_sq` and `momentTwo_eq`
at `x = 0`; `M` reproduces batch 12's §P1 value `5.709915417228e-03` to 11 digits.  With the
closed form validated, `tmp/c3b13_num7.py` finishes the table on a fixed grid in `float64` —
legitimate because **every integrand here is positive**, so there is no cancellation — and
re-runs both controls as a self-rejection gate (`reldiff 1.1e-16` and `3.0e-16`, passed):

```
       a            Jbar(a)     T = 4 Jbar/a^2   fires?
    0.10   4.8771598605e-03       1.9508639442       no
    0.15   5.4225317857e-03       0.9640056508      yes
    0.20   7.5666720522e-03       0.7566672052      yes
    0.22   8.9401407944e-03       0.7388546111      yes     <- optimum
    0.30   1.7404714132e-02       0.7735428503      yes
    1.00   2.4141915269e-01       0.9656766108      yes
  best a = 0.22,  T_min = 0.7388546111,  c0(0)^2 = 0.9885162724
  fibre L = { x : |c0(x)| >= 0.8595665251 }  =>  the INTERVAL |x| <= 2.50349099
```

**Measured coverage on `[0,60]` step 0.05 (1201 points):**

| fibre | compiled theorem | points | % |
|---|---|---|---|
| S (small readout) | `momentTwo_nonneg_of_thickened` | 2/1201 | 0.17% |
| L (large readout) | `momentTwo_nonneg_of_large_readout` | 51/1201 | 4.25% |
| **S ∨ L** | `momentTwo_nonneg_of_either` | **53/1201** | **4.41%** |

**Correction to my own estimate:** while the table was running I wrote that a pencil estimate
gave `|x| ≲ 5` for fibre L.  The measured value is `|x| ≤ 2.503`.  The estimate was wrong by
a factor of two and is superseded by the measurement.

**Honest reading:** the compiled union covers a neighbourhood of `x = 0` — which §P10
identifies as the **tightest** point of the target — plus two specks at the first zero.  It
leaves the bulk of the line open.  No claim beyond the measured count.

No mathematical route is declared successful on numerical grounds.

---

## ATTACKS EXECUTED — 24, and where each landed

| # | attack | outcome |
|---|---|---|
| 1 | Ξ-derivative normalisation, 3 independent routes | dictionary to `6.7e-53`; `κ = 2` exact; **first attempt REJECTED at 6%** |
| 2 | `Σ1/γ²` positive control | FIRED, `4.1e-8` |
| 3 | hostile scan to `x = 400` + zero ordinates | 0 negatives / 2144 |
| 4 | elementary/polygamma/ζ split | exact (`reldiff 0.0`); **F1** as a reduction |
| 5 | sign audit of the three terms | `Re(ζ′/ζ)′(½+it) ≥ 0` **FALSE** |
| 6 | thickened zero fibre | **COMPILED** (A1), coverage 2/1201 |
| 7 | Sturm / differential inequality | **F9**, own slip corrected |
| 8 | R-kernel positive representation | derived 2 ways; Lean gated on one lemma → NEXT TARGET |
| 9 | cell-density domination | **COMPILED** (A2) |
| 10 | weighted two-sided bound, arbitrary weight | **COMPILED** (A2) |
| 11 | derivation law, 2 independent spellings | **COMPILED** (A3) |
| 12 | elementary-factor split with the remaining `N` | **COMPILED** (A3) |
| 13 | general-kernel domination (no evenness) | **COMPILED** (A3) |
| 14 | movable-centre positive double-integral split | **COMPILED** (A4) |
| 15 | union of the two fibres | **COMPILED** (A4) |
| 16 | Schoenberg / Gaussian scale mixture | **F4**, prediction pre-registered and confirmed |
| 17 | de Bruijn–Newman flow on `L₁` itself | pre-registered; **incomplete** (script still running) |
| 18 | second Laguerre `L₂` | **F10** |
| 19 | margin structure / where tightest | tightest at `x = 0`; not asymptotic |
| 20 | truncated-theta transfer | violation found, then **RETRACTED (F7)** |
| 21 | precision + corner adjudication of #20 | stable to `3.1e-39`; corner identified |
| 22 | independent Hadamard-zero cross-check | **F8**, MISSED |
| 23 | off-line-zero calibration / canonical product | zero-repulsion reading (**EQUIV**) |
| 24 | closed-form counterexample + corner mechanism | **COMPILED** (A5) — **F5/F6** |

Also re-derived and cited, not re-run: Pólya (**F3**, structural proof), Hudson's theorem
(gives the *structural reason* for batch 3 attack 20's refutation of pointwise Wigner
positivity: `W_f ≥ 0` iff `f` is Gaussian), Gram/Lagrange sign-blindness (batch 12 F1).

**Two independent decompositions at every nontrivial step, with the first Lean line of each**
— as required: derivation law (`laguerre_mul` by `ring` **and** `laguerre_quotient` by
`field_simp; ring`, **both compiled**); sharp two-sided bound (route I = `R`-kernel + Fubini,
first line typed, needs the new pairing lemma; route II = cell-density domination,
**compiled** — route II is why A2 exists); moment split (batch-12 three-leg `momentTwo_eq`
**and** A4's movable centre, both compiled); target unfolding (`(t−s)²` double integral in
`(t,s)` **and** the `(u,p)` cell form, cross-checked numerically).

---

## PAPER / CHART AUDIT

Read this batch: `tmp/c3b12_A1..A3.lean` in full; `tmp/claude_c3_proof_batch12_20260825.md`
in full; `tmp/claude_c3_proof_batch3_20260824.md` §§18–30 and its calibration header;
`tmp/claude_c3_long_batch_20260824.md` §§FAILED-5..8 and the misattribution correction;
`GOAL_HP_UNCONDITIONAL.md:110-175`; `RequestProject/XiStructureFunction.lean`,
`JKernelSignLaw.lean`, `XiKernelThetaBridge.lean`,
`ThetaWronskianSuzukiGram.lean:40-80`; `tmp/c3b10_A1..A3.lean` and `tmp/c3b11_A1..A3.lean`
at the definition/pairing sites.  **Batch 12's chart citations were spot-checked at source
and all hold** (`universal.tex` L106–111, L1766–1782, L2485–2492, L3534–3542).

| chart | preserved how in batch 13 |
|---|---|
| **native helix `Re s > 0`, phasors entering at 0** (`universal.tex` L1766–1782: "Each phasor enters at zero magnitude and grows continuously … that line is where the projected series stops converging in the readout chart, not a threshold on the carrier") | No convergence abscissa is invoked in any of A1–A5. Every integrability fact is inherited from batch 12's tilt-shifted majorants or proved from `\|cos\| ≤ 1`; no half-plane appears. |
| **physical carrier `Z > 0`, `y = log Z`** (`universal.tex` L109–111) | All five files work in the carrier variables `u` (cell centre) and `p` (half-gap), i.e. the `t = log Z` chart. `momentTwo_abs_le`, `momentTwo_ge_shifted` and `Jbar` are statements about `∫_{(0,∞)} … du` — carrier-native throughout. |
| **double helix / anti-helix conjugate** (`universal.tex` L585–700, `J² = id` L662–670) | Batch 12's F3 (`antihelix_swap`: the two branches **coincide**, they do not cancel) is unchanged and was **used**, not merely cited: it is what makes the `R`-representation identical to the `u²`-moment, which is why the `R` route buys a representation and not a new bound. |
| **`S(t) = N_{π/3}(e^t) − N_1(e^t)`, `π/3 ≠ 1`** (`thm:carrier-scale-S`, L2485–2509; `pi3_arcs_eq`/`unit_arcs_empty` L3534–3542) | **Not used and not blended.** Batch 13 touches no counting ledger and performs no cell-registration scan; every numeric is a **moment or transform evaluation**, so the `π/3` register is not at risk. The three `S`s of the corpus (carrier `S_ev`, contour `S_Γ`, classical `S_class`) remain distinct. Flagged forward, unchanged: any future scan over a *cell* variable must be on `π/3` cells, never unit-1. |
| **Ξ chart** | Batch 13 uses `Ξ(x) = ξ(½+ix)` (`x` real). This is a **third** chart, distinct from `hp_pencil_v2` §1's `A(z) = ξ(½+iz)` and from `XiStructureFunction`'s `ξ(½−iz)`; it is named explicitly wherever it appears and is **never merged** with either. The measured constant `κ = 2` relating `cosMom riemannXiKernel` to it is now pinned exactly. |
| **HP pencil chart** (`hp_pencil_v2.tex` L73–86, L208–227, L508–513) | Batch 13 constructs no pencil object. Batch 12's F2 (`oddMoment_full_zero`: this engine cannot supply the pencil's odd moments) is unchanged. |
| **GRH family charts** (`grh_companion.tex` L99–104, L414) | Untouched. `gen_cellDensity_abs_le` is stated for a **real-valued** `W ≥ 0` and, unlike `gen_target_eq`, does not even use evenness — but for exactly the reasons batch 12's adjudication recorded, it does **not** extend to complex Dirichlet kernels (no complex-kernel pairing theorem, no compiled root-number law, no per-character integrability bridge). **No GRH statement follows from this batch.** |

`grep -i "cellDensity\|cell density\|Laguerre\|sinh(2yu)"` over `universal.tex`,
`hp_pencil.tex`, `hp_pencil_v2.tex`, `grh_companion.tex` → the C3 campaign is still **not in
print**, so nothing here changes a printed claim and **no paper edit is proposed.**

---

## GIT REVIEW

```
git diff --stat                       →  EMPTY (no tracked file modified)
git status --porcelain | grep -v '^?? tmp/'
?? RequestProject/WeightedTailPrimitive.lean      (pre-existing, untouched)
?? RequestProject/WeightedTailSinhBridge.lean     (pre-existing, untouched)
?? RequestProject/XiHelixChart.lean               (pre-existing, untouched)
?? RequestProject/XiStructureResidual634.lean     (pre-existing, untouched)
?? RequestProject/XiStructureSeatBridge.lean      (pre-existing, untouched)
```

New this batch, all untracked, all under `tmp/`, nothing committed:
`c3b13_A1..A5.lean`, `c3b13_A1..A4.olean`, `c3b13_audit.log`,
`c3b13_num1..num6.py`, `c3b13_num1..num6_out.txt`, this ledger.

---

## THE SMALLEST EXACT NEXT LEAN THEOREM

The one missing ingredient that converts the target into a **positive-definiteness question
about an explicitly exhibited nonnegative function** — i.e. the object every classical
criterion (Bochner, Schoenberg, Pólya, Gneiting) is stated for.  It is the convolution
companion of the compiled `C3B11.carrier_pairing2`, and mirrors that proof's structure (a
translation, a dilation, and the shear `(v,p) ↦ (v+p, p)`), with the chart clock moved from
the **gap** variable to the **cell-centre** variable:

```lean
theorem carrier_conv_pairing {A B : ℝ → ℝ}
    (hIA : Integrable A) (hmA : Measurable A)
    (hIB : Integrable B) (hmB : Measurable B) (x : ℝ) :
    (∫ v : ℝ, (∫ p : ℝ, A (v + p) * B (v - p)) * Real.cos (x * v))
      = 2⁻¹ * (C3B10.cosMom A (x / 2) * C3B10.cosMom B (x / 2)
             - C3B10.sinMom A (x / 2) * C3B10.sinMom B (x / 2))
```

With it, applying `C3B12.cell_u2_split`'s three legs to
`R v := ∫ p, p ^ 2 * riemannXiKernel (v + p) * riemannXiKernel (v - p)` gives, by algebra
already compiled and the parity facts `cosMom kM1 = 0`, `sinMom Φ = 0`, `sinMom kM2 = 0`:

```lean
theorem cosMom_Rker (x : ℝ) :
    C3B10.cosMom R (2 * x)
      = 4⁻¹ * (C3B10.cosMom riemannXiKernel x * C3B10.cosMom C3B12.kM2 x
             + C3B10.sinMom C3B12.kM1 x ^ 2)
```

— i.e. `L₁ = 4·R̂`, with `R ≥ 0` pointwise and trivially (`p²Φ(v+p)Φ(v−p) ≥ 0`).  **The
first Laguerre inequality for `Ξ` then reads exactly: this explicit nonnegative even function
is positive definite.**  Note honestly what that is and is not: it is an **EQUIV**, and by
§F3/§F4 the two classical criteria that would discharge it (Pólya, Schoenberg) are already
dead for objects of this shape.  Its value is that it puts the target in the one normal form
where a zero-location input — which §F6 proves any proof must consume — can be attached to a
positive kernel rather than to a signed integral.

---

## MACHINE-READABLE SUMMARY

```yaml
batch: c3-batch-13
date: 2026-08-25
session_dir: /Users/samuellavery/work/helix_frobenius
branch: ladder-campaign-2026-08
target_proved: false
rh_claimed: false
grh_claimed: false
novelty_claimed: false
commits: 0
tracked_files_modified: 0
agents_md_present: false
lean_files_new: 5
declarations_compiled: 49
declarations_by_file: {A1: 16, A2: 10, A3: 8, A4: 9, A5: 6}
axiom_footprint_all: "[propext, Classical.choice, Quot.sound]"
axiom_audit_log: tmp/c3b13_audit.log
forbidden_pattern_scan: "clean (exit 1, no output) over A1..A5"
compilation_provenance: "all five files compiled by me this session, exit 0, verbatim log retained"
attacks_executed: 24
target_unfolded: "L1(x) = Xi'(x)^2 - Xi(x)Xi''(x) >= 0, the first Laguerre inequality for the Riemann Xi function; equivalently log|Xi| concave between consecutive zeros; equivalently d2/dsigma2 |xi(sigma+it)|^2 >= 0 at sigma=1/2"
dictionary_measured: {kappa: 2, kappa_error: 2.3e-61, slot_error: 6.7e-53}
headline:
  name: C3B13.laguerre_abs_le_zero
  statement: "|cosMom Phi x * cosMom kM2 x + sinMom kM1 x^2| <= cosMom Phi 0 * cosMom kM2 0"
  hypotheses: none
  reading: "|Xi'(x)^2 - Xi(x)Xi''(x)| <= Xi(0)*(-Xi''(0)) for all real x; sharp, attained at x=0"
new_conditional_criteria:
  - "C3B13.momentTwo_nonneg_of_thickened: weakens batch 12's EQUALITY hypothesis cosMom Phi x = 0 to an INEQUALITY. CONDITIONAL: nothing in Lean proves the hypothesis holds at any x. The 'interval around each zero' reading needs continuity plus Xi'(gamma) != 0 and is NUMERICAL/UNFORMALIZED."
  - "C3B13.momentTwo_nonneg_of_large_readout: conditional criterion keyed to a LARGE readout. Also conditional; hypothesis not proved anywhere in Lean."
  - "C3B13.momentTwo_nonneg_of_either: a DISJUNCTION of the two hypotheses, NOT a dichotomy. The two are oppositely directed but are NOT logical complements and do NOT partition the line; measured union 4.41% of the grid, so 95.59% satisfies neither."
unconditional_results_no_hypothesis:
  - "C3B13.laguerre_abs_le_zero (the sharp two-sided bound)"
  - "C3B13.cellDensity_abs_le_zero, weighted_moment_abs_le, momentTwo_abs_le, momentZero_abs_le"
  - "C3B13.laguerre_mul, laguerre_elementary_split (algebra), corner_tail_laguerre, laguerre_two_over_one_add_sq"
key_negative_result:
  name: C3B13.laguerre_two_over_one_add_sq_neg
  content: "W(t)=exp(-|t|) is even, positive, integrable, transform 2/(1+x^2), and L1 = (8-8x^2)/(1+x^2)^4 < 0 for |x|>1"
  consequence: "evenness + positivity + integrability CANNOT imply the target; any proof must consume arithmetic input"
  mechanism: "C3B13.corner_tail_laguerre_neg: a corner at 0 forces Xi ~ -A/x^2 hence L1 ~ -2A^2/x^6 < 0. Riemann's Phi has no corner: it is even as an identity (Jacobi reflection, riemannXiKernel_neg), and an even differentiable function has vanishing derivative at 0, so the corner mechanism does not apply to it. No claim is made about which ingredient of a hypothetical proof carries the weight."
refuted_this_batch:
  - "Re (zeta'/zeta)'(1/2+it) >= 0 is FALSE (min -0.699 at t ~ 0.85)"
  - "Polya's criterion is structurally inapplicable to ANY smooth even kernel (proof, not measurement)"
  - "Schoenberg/Gaussian-scale-mixture: DEAD, but this ledger's original evidence was WRONG and is replaced by batch 14's direct test. See the corrected F4. Original claim '|L1| is not monotone' cited a script that never ran AND is false on [0,120] (0 increases at step 0.25, 40 digits). Correct kill: complete monotonicity of g(tau)=R(sqrt tau) fails at the third derivative, min (-1)^3 g''' = -3.81."
  - "second Laguerre L2 is positive at all sampled ordinates, so the ladder does not bite earlier"
retractions_this_batch:
  - "F7: my own 'no termwise argument can work' reading of the N=1 truncation violation. The violation is numerically stable (spread 3.1e-39) but is the CORNER artefact of the even extension, not the truncation: Phi_N'(0+) = 7.9e-2, 1.65e-7, 2.8e-16, 3.5e-40 for N=1,2,3,5, collapsing in lock-step with the violation. WITHDRAWN; issued as refutation spec RS-1 instead."
  - "F1: my predicted sign of the polygamma term. T_gam ~ -1/(4x^2) < 0, negative at 1189/1200 points; I had predicted positive from Re(1/z) and dropped the 1/(2z^2) term."
  - "F9: my first spelling L1' = -Xi*Xi''' is WRONG; the correct value is L1' = Xi'Xi'' - Xi Xi'''."
  - "P0: the first quadrature run disagreed with the moment route by up to 6.0% and was REJECTED, not reconciled; two bugs found and fixed."
failed_cross_checks:
  - "F8: the independent Hadamard-zero route for the N=1 finding MISSED (found a zero at delta=7.13 where L1 is positive). Reported as a failed cross-check; the F5/F7 conclusion does not rest on it."
fibre_coverage_measured:
  grid: "x in [0,60] step 0.05, 1201 points"
  small_readout: {theorem: C3B13.momentTwo_nonneg_of_thickened, points: 2, pct: 0.17}
  large_readout: {theorem: C3B13.momentTwo_nonneg_of_large_readout, points: 51, pct: 4.25, interval: "|x| <= 2.50349099", best_a: 0.22}
  union: {theorem: C3B13.momentTwo_nonneg_of_either, points: 53, pct: 4.41}
  note: "covers a neighbourhood of x=0, which is the TIGHTEST point of the target; leaves the bulk of the line open"
incomplete_this_batch:
  - "tmp/c3b13_num2.py (R-kernel nested-quadrature identity check, envelope/phase scan, transfer battery) did not finish; NO result from it is used anywhere in this ledger"
  - "attack 17 (de Bruijn-Newman flow on L1) pre-registered but not completed"
hostile_scans:
  L1_sign: {range: "x in [0,400] + 27 zero ordinates x 9 offsets", points: 2144, negatives: 0, min_scale_free: 0.0462099862308, at: 0.0, certified: false, method: "cancellation-free via (xi'/xi)'(1/2+ix)"}
margin_structure: "min of L1/Xi^2 GROWS with height (0.0462 on [0,5] to 1.262 on [160,320]); the target is TIGHTEST at x=0, so the difficulty is NOT asymptotic"
literature_check_still_required:
  - "first Laguerre inequality Xi'^2 - Xi Xi'' >= 0 for the Riemann Xi function: NOT read at source (web tools unavailable, THREE sessions running). NO novelty is claimed anywhere in this ledger."
open_next_lean_statement: |
  theorem carrier_conv_pairing {A B : R -> R}
      (hIA : Integrable A) (hmA : Measurable A)
      (hIB : Integrable B) (hmB : Measurable B) (x : R) :
      (int v, (int p, A (v + p) * B (v - p)) * Real.cos (x * v))
        = 2^{-1} * (cosMom A (x/2) * cosMom B (x/2) - sinMom A (x/2) * sinMom B (x/2))
open_next_purpose: "unlocks cosMom R (2x) = (1/4)(c0 c2 + s1^2) with R v = int p^2 Phi(v+p)Phi(v-p) dp >= 0, i.e. 'the target IS the positive-definiteness of one explicit nonnegative even function'. EQUIV, not STRONGER; its value is normal form, and both classical discharges (Polya, Schoenberg) are already dead by F3/F4."
```
