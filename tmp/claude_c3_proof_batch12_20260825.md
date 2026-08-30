# C3 proof batch 12 — the even-moment ladder, and the first strictly-weaker sub-leaf

> ## ⚠ ADJUDICATION CORRECTIONS APPLIED 2026-08-25 (OpenAI review) — READ FIRST
>
> Six defects were found in the first version of this ledger and its artifacts.  All six are
> corrected below **and in the source files**.  Summary, so nothing is read stale:
>
> | # | defect | status |
> |---|---|---|
> | 1 | A3 claimed arbitrary Dirichlet/automorphic character kernels follow "for free" and the engine is "character-blind" | **WITHDRAWN.** `gen_target_eq` is a **real-valued** even-kernel theorem. Complex characters need a complex-kernel theorem, a root-number/conjugation law, and their own integrability bridge — none exist here. |
> | 2 | ledger proposed `0 ≤ cosMom Φ x · cosMom kM2 x` as the "smallest sub-fibre" | **FALSE, moved to FAILED (F11).** Refuted at `x = 7` by this ledger's own P2 table; `c₀c₂ < 0` on **50.0%** of a 1201-point grid. OPEN reverts to the full edge `c₀c₂ + s₁² ≥ 0`. |
> | 3 | A2's elementary-factor split presented as if the analytic bridge were compiled | **MARKED UNCOMPILED** in A2's header, in `c3b12_num.py`, and here. Only the complex-algebra identity compiles. |
> | 4 | `oddMoment_full_zero` proved by parity with no integrability — exploits Lean's zero-convention | **REPAIRED.** `u_cellDensity_integrable` now compiles genuine integrability from the engine, and the value comes from the pairing. |
> | 5 | P4's `1.246110e-194` at `x = 300` computed at 30 dps | **CROSS-CHECKED** at 80/120 dps and reported scale-free; **labelled NON-CERTIFIED regardless.** |
> | 6 | `c3b12_num.py` printed a stale "outside the disc both are positive" | **FIXED IN THE SCRIPT** and rerun, not only in the ledger. |
>
> **COMPILATION STATUS OF THE CORRECTED LEAN — INDEPENDENTLY VERIFIED.**  `lake env lean` was
> gated behind approval in my session, so the corrected `tmp/c3b12_A2.lean` and
> `tmp/c3b12_A3.lean` were **compiled independently by the OpenAI adjudicator**, exit code 0:
>
> * **A2: all 17 declarations** printed exactly `[propext, Classical.choice, Quot.sound]`.
> * **A3: all 8 declarations** printed exactly `[propext, Classical.choice, Quot.sound]`.
> * **Escape scan** over A1/A2/A3: exit 1, no output — no
>   `axiom` / `sorry` / `admit` / `implemented_by` / `native_decide` hits.
>
> `tmp/c3b12_A1.lean` is unchanged from my own compiled run (19 declarations, same footprint).
> **Total: 44 declarations, all at the standard footprint.**  Provenance is recorded honestly:
> A1's audit is mine, A2's and A3's are the adjudicator's.

Date 2026-08-25.  `/Users/samuellavery/work/helix_frobenius`, branch `ladder-campaign-2026-08`.
**No commit.  No tracked file modified.  `tmp/c3b10_*` and `tmp/c3b11_A*.lean` untouched.**
(`AGENTS.md` still does not exist in this repository; `CLAUDE.md` obeyed.)

TARGET LEAF, unchanged: `0 ≤ ∫ u in Ioi 0, u*sinh(2*y*u) * C3B6.Theta.cellDensity x u`
for all real `x`, `y ≥ 0`.  Batch 11 reduced it to the exact scalar inequality
`0 ≤ cosMom(wQ y,x)·cosMom(wP y,x) + sinMom(wS y,x)·sinMom(wR y,x)`.

**HEADLINE.**  The even moments of the cell density are the **Laguerre expressions of the
readout**, compiled exactly; the `k = 1` member is a strictly weaker sub-leaf; and the
batch-11 counterexample **does not obstruct it** — a second counterexample shows what still
does.  40 new declarations, all axiom-clean.

---

## 0. CORRECTIONS TO BATCH 11 (applied in place, in `tmp/claude_c3_proof_batch11_20260825.md`)

1. **Normalisation.**  `Q = Re[M′·conj M] = ½ d/dy|M|²`, so
   `Q/|M|² = ½ d/dy log|M|² = d/dy log|M| = Re[ξ′/ξ]`.  Batch 11 printed
   `Q/|M|² = 2·d/dy log|M|` — **wrong factor 2**.  Scan results unaffected (only `sign(Q)`
   was used, and `Q = |M|²·Re[ξ′/ξ]` is computed exactly).  Fixed in the ledger and in
   `tmp/c3b11_num2.py`.
2. **The `x = 0` scan row is a numerical limit at `x = 1e-6`.**  The closed form
   `ξ′/ξ = 1/s + 1/(s−1) − ½logπ + ½ψ(s/2) + ζ′/ζ(s)` has a **removable** singularity at
   `s = 1` (the pole of `1/(s−1)` cancels the pole of `ζ′/ζ = −1/(s−1)+O(1)`), but each
   summand is separately singular and `(x,y) = (0,½)` is exactly `s = 1`; `mpmath` raises
   `zeta(1) pole` there.  Now labelled as a limit in both files.
3. **The Gaussian-mixture claim is withdrawn and restricted to the explicit example.**
   Batch 11 asserted that every Gaussian mixture but a single Gaussian fails the target.
   Two gaps: entirety/finite order of `M` was assumed, not derived; and the Hadamard step
   needs that order bound.  Only `Φ_g = e^{−t²} + e^{−4t²}` survives, by closed form.

---

## COMPILED

Build command for every file: `LEAN_PATH=tmp lake env lean -o tmp/<f>.olean tmp/<f>.lean`.
All `#print axioms` lines below are verbatim compiler output; no `error:` lines in any run.

### `tmp/c3b12_A1.lean` — the even-moment ladder (19 declarations)

`(2u)^{2k} = ((u+p)+(u−p))^{2k}` expands binomially into two-leg products, so batch 11's
`carrier_pairing2` evaluates every even moment exactly.  At `k = 1`, with `M_j(t) = t^jΦ(t)`:

```lean
theorem cell_u2_split (u p : ℝ) :
    kM2 (u + p) * riemannXiKernel (u - p) + 2 * (kM1 (u + p) * kM1 (u - p))
      + riemannXiKernel (u + p) * kM2 (u - p)
      = 4 * (u ^ 2 * (riemannXiKernel (u + p) * riemannXiKernel (u - p)))

theorem momentTwo_eq (x : ℝ) :                       -- hypotheses: NONE
    (∫ u in Ioi (0 : ℝ), u ^ 2 * cellDensity x u)
      = 8⁻¹ * (cosMom riemannXiKernel x * cosMom kM2 x + sinMom kM1 x ^ 2)
```

In readout coordinates `Ξ(x) = ∫Φ(t)cos(xt)dt` the dictionary is `c₀ = Ξ`, `s₁ = −Ξ′`,
`c₂ = −Ξ″` (measured, §P2 below), so the bracket is **`Ξ′(x)² − Ξ(x)Ξ″(x)`: the first
Laguerre expression**.  General `k` gives
`∫_ℝ u^{2k}C = 2^{−2k−1}·Σ_{j}(−1)^{j+k}\binom{2k}{j}Ξ^{(j)}Ξ^{(2k−j)}`, the `k`-th Laguerre
expression (derived on paper; only `k = 0, 1` compiled).

Three unconditional consequences, all with no hypothesis beyond what is displayed:

```lean
theorem cellDensity_Ioi_eq_sq (x : ℝ) :              -- batch 10's first tail is ONE square
    (∫ u in Ioi (0 : ℝ), cellDensity x u) = 4⁻¹ * cosMom riemannXiKernel x ^ 2

theorem momentTwo_ge (x : ℝ) :                       -- the sine channel is a square floor
    8⁻¹ * (cosMom riemannXiKernel x * cosMom kM2 x)
      ≤ ∫ u in Ioi (0 : ℝ), u ^ 2 * cellDensity x u

theorem momentTwo_eq_sq_of_cosMom_zero {x : ℝ} (hx : cosMom riemannXiKernel x = 0) :
    (∫ u in Ioi (0 : ℝ), u ^ 2 * cellDensity x u) = 8⁻¹ * sinMom kM1 x ^ 2
theorem momentTwo_nonneg_of_cosMom_zero {x : ℝ} (hx : cosMom riemannXiKernel x = 0) :
    0 ≤ ∫ u in Ioi (0 : ℝ), u ^ 2 * cellDensity x u
```

**The zero fibre is the sharp one.**  At every real `x` where the readout's cosine moment
vanishes — i.e. at every real zero of `Ξ` — the second moment is a *perfect square*,
`⅛·(sinMom (tΦ) x)² = ⅛Ξ′(x)²`.  That is exactly where a Laguerre-type inequality is most
delicate, and there it closes by identity, unconditionally.  Verified numerically at six zero
ordinates to `|d| ≤ 2.4e-15` relative (§P4).

Verbatim footprint (19/19):

```
'C3B12.sq_le_four_mul_exp' depends on axioms: [propext, Classical.choice, Quot.sound]
'C3B12.sq_le_four_mul_exp_add_exp' depends on axioms: [propext, Classical.choice, Quot.sound]
'C3B12.xiKernel_integrable' depends on axioms: [propext, Classical.choice, Quot.sound]
'C3B12.kM1_integrable' depends on axioms: [propext, Classical.choice, Quot.sound]
'C3B12.kM2_integrable' depends on axioms: [propext, Classical.choice, Quot.sound]
'C3B12.sinMom_xiKernel' depends on axioms: [propext, Classical.choice, Quot.sound]
'C3B12.cosMom_kM1' depends on axioms: [propext, Classical.choice, Quot.sound]
'C3B12.sinMom_kM2' depends on axioms: [propext, Classical.choice, Quot.sound]
'C3B12.cellDensity_Ioi_eq_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'C3B12.cell_u2_split' depends on axioms: [propext, Classical.choice, Quot.sound]
'C3B12.u2_cellDensity_ae' depends on axioms: [propext, Classical.choice, Quot.sound]
'C3B12.u2_cellDensity_integrable' depends on axioms: [propext, Classical.choice, Quot.sound]
'C3B12.u2_cellDensity_full' depends on axioms: [propext, Classical.choice, Quot.sound]
'C3B12.momentTwo_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'C3B12.momentTwo_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'C3B12.momentTwo_nonneg_of_cos' depends on axioms: [propext, Classical.choice, Quot.sound]
'C3B12.momentTwo_eq_sq_of_cosMom_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'C3B12.momentTwo_nonneg_of_cosMom_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'C3B12.momentTwo_zero_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### `tmp/c3b12_A2.lean` — structural attacks (13 declarations)

```lean
theorem elementary_factor_split (c : ℝ) (z N Nd : ℂ) :        -- hypotheses: NONE
    ((z * N + z * N + (z ^ 2 - (c : ℂ)) * Nd) * (starRingEnd ℂ) ((z ^ 2 - (c : ℂ)) * N)).re
      = 2 * z.re * (Complex.normSq z - c) * Complex.normSq N
        + Complex.normSq (z ^ 2 - (c : ℂ)) * (Nd * (starRingEnd ℂ) N).re
theorem elementary_term_nonneg {y x n : ℝ} (hy : 0 ≤ y) (hd : 4⁻¹ ≤ y^2+x^2) (hn : 0 ≤ n) : ...
theorem elementary_term_neg    {y x n : ℝ} (hy : 0 < y) (hd : y^2+x^2 < 4⁻¹) (hn : 0 < n) : ...

theorem lagrange_identity (A A' B B' : ℝ) :
    (A*A' + B*B')^2 + (A*B' - B*A')^2 = (A^2+B^2)*(A'^2+B'^2)
theorem antihelix_swap (u p : ℝ) :
    riemannXiKernel (p+u) * riemannXiKernel (p-u) = riemannXiKernel (u+p) * riemannXiKernel (u-p)
theorem modeLam_diag (n : ℕ) : modeLam n n = 0
theorem leaf_eq_re (A A' B B' : ℝ) :
    A*A' + B*B' = (((A':ℂ) + (B':ℂ)*Complex.I) * conj ((A:ℂ) + (B:ℂ)*Complex.I)).re
```

> **`elementary_factor_split` IS ALGEBRA ONLY (adjudication item 3).**  It is a statement
> about three arbitrary complex numbers `z, N, Nd`.  The **analytic bridge** that would
> instantiate it at the actual `Ξ`-kernel — `M(z) = (z²−¼)N(z)` with `N(z) = ∫ψ(t)e^{zt}dt`,
> from integrating by parts twice against `Φ = ψ″ − ψ/4` — is **NOT COMPILED**: it needs
> decay of `ψ, ψ′` to kill boundary terms and a differentiation-under-the-integral step,
> neither formalised.  It is pencil reasoning plus the §P3 numerical check.  Everywhere the
> factorisation appears — A2's header, `c3b12_num.py`, this ledger — it is now so marked.

**Added by the adjudication pass (item 4 — the integrability repair):**

```lean
theorem u_cellDensity_integrable (x : ℝ) : Integrable (fun u : ℝ => u * cellDensity x u)
theorem oddMoment_full_zero (x : ℝ) : (∫ u : ℝ, u * cellDensity x u) = 0
```

The first draft proved `oddMoment_full_zero` by parity with **no integrability hypothesis**.
That is inadmissible: Lean's Bochner integral is `0` by convention on non-integrable
functions, so the statement was true for a reason carrying no analytic content.  Repaired by
routing the first moment through the *same* two-weight engine — the split `2u = (u+p)+(u−p)`
gives two legs, `carrier_pairing2_integrable` gives genuine integrability, and
`carrier_pairing2` gives the value `0` from `cosMom kM1 = 0` and `sinMom Φ = 0`.  No
zero-convention anywhere.

**Also added (item 2 — the honest reduction):** `momentTwo_nonneg_of_square_dominates`.

Footprint: **A2 compiles at exit 0 with all 17 declarations at exactly
`[propext, Classical.choice, Quot.sound]`** (independently verified by the OpenAI
adjudicator after the corrections).  The 13 original declarations —
`elementary_factor_split, elementary_scalar, elementary_term_nonneg, elementary_term_neg,
lagrange_identity, gram_det_eq, antihelix_swap, antihelix_cellDensity, modeLam_diag,
modeLam_diag_cos, oddMoment_full_zero, leaf_eq_re, rotation_eq_im` — plus the four added by
this pass: `cell_u1_split, u_cellDensity_ae, u_cellDensity_integrable,
momentTwo_nonneg_of_square_dominates`.

### `tmp/c3b12_A3.lean` — the leaf identity for an **arbitrary even kernel** (8 declarations)

```lean
theorem gen_target_eq (hm : Measurable W)
    (hQ : ∀ y, Integrable (gQ W y)) (hS : ∀ y, Integrable (gS W y))
    (hP : ∀ y, Integrable (gP W y)) (hR : ∀ y, Integrable (gR W y))
    (hev : ∀ t : ℝ, W (-t) = W t) (x y : ℝ) :
    (∫ u in Ioi (0 : ℝ), gY y u * genCell W x u)
      = 4⁻¹ * (cosMom (gQ W y) x * cosMom (gP W y) x
          + sinMom (gS W y) x * sinMom (gR W y) x)
```

Every hypothesis displayed; nothing arithmetic, nothing about zeros.

> **SCOPE, CORRECTED (adjudication item 1).**  The first version of this ledger called this
> "the **GRH/character generalization**: any Dirichlet or automorphic completed kernel is
> admissible with no new work — the engine is prime-blind and character-blind."  **That is
> withdrawn.**  `W : ℝ → ℝ` is **real-valued**, `hev` is `W(−t) = W(t)`, and every ingredient
> (`cosMom`, `sinMom`, `carrier_pairing2`) is real.
>
> A **complex** Dirichlet character's theta kernel is complex-valued and does *not* satisfy
> `W(−t) = W(t)`; its reflection law relates the kernel of `χ` to that of `χ̄` through the
> root number `ε(χ)`.  Extending the leaf identity there requires three things **that do not
> exist in this repository**:
> 1. a **complex-kernel** two-weight pairing theorem — `carrier_pairing2` re-proved for
>    `ℝ → ℂ` with `conj` in the correct slot, since the `χ`/`χ̄` pairing gives `M·conj M`
>    rather than a square;
> 2. the compiled **root-number / conjugation law** `W_χ(−t) = ε(χ)·W_{χ̄}(t)` (or its
>    completed analogue) replacing `hev`;
> 3. a **per-character integrability bridge** — batch 10's Gaussian majorant is proved for
>    `riemannXiKernel` alone, and a conductor-dependent majorant would have to be established.
>
> What *is* covered with no new work: real even kernels — the trivial character, and any
> **real (quadratic)** character's kernel once evenness and the four integrabilities are
> supplied.  **No GRH statement follows from this file.**

What the theorem *is* good for, unchanged: it is the exact statement of **the instrument's
limit**, because `Φ_c` satisfies every hypothesis and refutes the sign.

Footprint: **A3 compiles at exit 0 with all 8 declarations at exactly
`[propext, Classical.choice, Quot.sound]`** (independently verified by the OpenAI adjudicator
after the corrections): `gen_cell_weight_split, gQ_even, gS_odd, gP_even, gR_odd, gen_gY_ae,
gen_gY_full, gen_target_eq`.  This pass changed only the docstring; no proof term was touched.

### Deliverable scan

```
grep -n "sorry\|admit\|^axiom\|axiom \|implemented_by\|native_decide\|@\[implemented" \
     tmp/c3b12_A1.lean tmp/c3b12_A2.lean tmp/c3b12_A3.lean       →  exit 1, no output
```
Re-run over the **corrected** files by the OpenAI adjudicator: exit 1, no output — no
`axiom` / `sorry` / `admit` / `implemented_by` / `native_decide` hits.

**44 declarations, 44 at exactly `[propext, Classical.choice, Quot.sound]`**
(A1: 19, mine; A2: 17 and A3: 8, independently compiled by the adjudicator at exit 0).
No Prop-valued hypothesis appears on the target signature: `momentTwo_eq`,
`momentTwo_eq_sq_of_cosMom_zero`, `cellDensity_Ioi_eq_sq` take only real variables (and one
equation of reals).  `momentTwo_nonneg_of_square_dominates` carries an implication hypothesis
between real inequalities — a *reduction*, deliberately not on the target signature.

---

## OPEN

**The leaf, unchanged (batch 11):**
```lean
theorem leaf_sign (x : ℝ) {y : ℝ} (hy : 0 ≤ y) :
    0 ≤ C3B10.cosMom (C3B11.wQ y) x * C3B10.cosMom (C3B11.wP y) x
      + C3B10.sinMom (C3B11.wS y) x * C3B10.sinMom (C3B11.wR y) x
```

**The new, strictly weaker sub-leaf** — now stated purely in compiled moments, with the
square already split off:
```lean
theorem laguerre_edge (x : ℝ) :
    0 ≤ C3B10.cosMom riemannXiKernel x * C3B10.cosMom C3B12.kM2 x
      + C3B10.sinMom C3B12.kM1 x ^ 2
```
By `C3B12.momentTwo_eq` this is exactly `0 ≤ ∫_{(0,∞)} u²C(x,u)du`, and by the dictionary it
is `Ξ′² − ΞΞ″ ≥ 0`.  **It is strictly weaker than the leaf** — proved by separation, not
asserted: `Φ_c` refutes the leaf and satisfies this (§P5′).  `C3B12.momentTwo_eq_sq_of_cosMom_zero`
already discharges it on `{Ξ = 0}`, so what remains is the complement.

> **THE PREVIOUSLY PROPOSED "SMALLEST SUB-FIBRE" IS FALSE (adjudication item 2).**  This
> ledger proposed the sign of `cosMom Φ x · cosMom kM2 x = −Ξ(x)Ξ″(x)` as the next target.
> **It is negative on half the line.**  See FAILED §F11.  The OPEN statement is and remains
> the **full** edge `0 ≤ c₀c₂ + s₁²`; the square is not optional.

**The genuinely smallest useful decomposition** (and it asserts no sign that is not proved) is
the **sign split** on `c₀c₂`:

* on `{c₀·c₂ ≥ 0}` the sub-leaf is **already compiled** — `C3B12.momentTwo_nonneg_of_cos`;
* on `{c₀·c₂ < 0}` the entire remaining content is **square domination**
  `|c₀·c₂| ≤ s₁²`, and the reduction to it is `C3B12.momentTwo_nonneg_of_square_dominates`.

The open region is therefore `{x : Ξ(x)·Ξ″(x) > 0}`, measured at **50.0%** of a 1201-point
grid on `[0,60]` (§(2) below), first entered at `x ≈ 4.80`.  On that region the surviving
inequality holds with a comfortable scale-free margin: `min (c₀c₂+s₁²)/s₁² = 0.2952346509`
at `x = 10.8`.  That margin is the quantity a proof must reach; it is **not** a proof.

**Literature: STILL NOT CHECKED.**  No web access this session either.  The first Laguerre
inequality for `Ξ` (Csordas–Norfolk–Varga-adjacent) must be read at source before any
priority or status claim.  Carried forward from batch 11 as the top external action.

---

## EQUIV (navigation only — never a stop reason)

* **Full leaf ⟺ RH**, via `A+iB = M(y+ix)`, `M(z) = 2ξ(½+z)`, `leaf = Re[M′ conj M]`
  (batch 11 EQUIV; one uncompiled differentiation step).  Compiled repo home:
  `RequestProject/DVPSeatRealPart.lean:62 xi_logDeriv_one_sub_conj`.
* **Sub-leaf ⟹ nothing yet known to be RH-strength.**  This is the batch's structural gain:
  the separation `Φ_c` puts the sub-leaf strictly below the leaf, so the batch-11 equivalence
  argument does **not** transfer to it.  I make no claim that the sub-leaf is weaker than RH —
  only that the leaf's proof of equivalence does not apply.
* **`hp_pencil_v2` Prop. 3.5 (Stieltjes/Hankel form)** is a *different* finite instrument on
  the same zeros; `C3B12.oddMoment_full_zero` shows this engine cannot supply its odd moments.

---

## FAILED

**F11 (adjudication item 2). The product-sign route `0 ≤ c₀·c₂` is FALSE.**  This ledger
proposed the sign of `cosMom Φ x · cosMom kM2 x = −Ξ(x)Ξ″(x)` as the "smallest sub-fibre" of
the `u²` sub-leaf.  It is refuted **by this ledger's own P2 table**, which I failed to check
against my own proposal: at `x = 7`, `c₀ = +3.0440904857e-01` and `c₂ = −1.9494121616e-02`,
so `c₀·c₂ = −5.93418701392e-03 < 0`.  High-precision scan (`tmp/c3b12_num3_out.txt` §(2),
mpmath 40 dps, 1201 points, `x ∈ [0,60]` step 0.05): **`c₀·c₂ < 0` at 600/1201 points, 50.0%
of the grid**, first entered at `x ≈ 4.80`, with sign runs
`+[0,4.80) −[4.80,14.15) +[14.15,17.05) −[17.05,21.05) +[21.05,23.25) −[23.25,25.05) …`.

**The square term restores the sampled sum at every one of those points.**  At `x = 7`:
`s₁² = 1.16946144492e-02` and `c₀c₂ + s₁² = +5.7604274353e-03 > 0`.  Over the whole negative
region the scale-free margin is `min (c₀c₂+s₁²)/s₁² = 0.2952346509` at `x = 10.8` — a
measured margin, **not** a proof.

Consequence: the OPEN statement reverts to the **full** edge `0 ≤ c₀c₂ + s₁²`; the square is
not optional.  The genuinely smallest useful decomposition is the sign split recorded in
OPEN, whose negative branch is reduced by `C3B12.momentTwo_nonneg_of_square_dominates`.

**F1 (new). The Gram/Hankel instrument is provably sign-blind.**  `lagrange_identity`:
`(A A′+B B′)² + (A B′−B A′)² = (A²+B²)(A′²+B′²)`.  A Gram determinant measures the length;
the leaf is the *orthogonal component*.  Compiled, not asserted.

**F2 (new). The half-line odd moments are outside the engine.**  `oddMoment_full_zero`:
`∫_ℝ u·C(x,u)du = 0` identically, so the full-line engine carries no information about
`∫_{(0,∞)} u·C`.  The Hankel/Stieltjes route needs exactly that.  A new device is required;
none was found.

**F3 (new). Helix/anti-helix conjugate cancellation does not exist here.**  `antihelix_swap`
compiles the exchange `p ↔ u`, under which the carrier product is invariant (`Φ` even), so
the two branches of the symmetrised leaf are **equal**, not opposite.

**F4 (new, and it corrects my own printed commentary). The elementary factor's sign flips at
`|s−½| = ½`, and so does the other term's.**  `elementary_factor_split` is exact to
`rel err ≤ 1.4e-28` (§P3).  The measured table shows the two terms have **opposite signs at
every sampled point**: inside the disc the elementary term is negative and the `Γζ` term
carries the leaf; outside, the elementary term is positive and the `Γζ` term is negative.
My script printed "outside, both are positive" — **that was wrong and the table refutes it.**

**F5 (new). A second counterexample: `Φ_g = e^{−t²}+e^{−4t²}` violates the SUB-leaf.**
`min L1_g = −1.559942194e-02` at `x = 3.25` (mpmath 40 dps, values of order `1`, so far above
any noise floor).  `Ξ_g > 0` everywhere, so `Φ_g` has no real zeros.  **Therefore the sub-leaf
is not implied by evenness + positivity either**, and any proof of it must use a property of
`Φ_Ξ` beyond positivity.

**F6 (RETRACTED numerics, mine).**  `tmp/c3b12_num.py` §P5 evaluated `L1_c` by central finite
differences with `h = 1e-4` on a quantity decaying like `e^{−x²/2}`, and printed
"106/401 negatives, min −1.17e-16".  **That is entirely roundoff** — at `x = 10.6` the true
scale is `~3.4e-17` and the differencing error is `~1e-16`.  Redone in closed form
(`tmp/c3b12_num2.py`): **0 negatives**.  Same failure mode as batch 11's first hostile scan;
the lesson repeats and is now a standing rule: *never finite-difference a doubly-decaying
kernel; get the closed form.*

**F7 (RETRACTED pencil, mine).**  The first draft of the `Φ_c` argument claimed
`h(c) = a(2c+a)/(2+ac)²` is maximised at `c = 1` with value `a/(2+a)`.  Wrong:
`h′(c) = 2a(2−ac−a²)/(2+ac)³`, so the max is at `c* = (2−a²)/a` with value `1/(4−a²)`.
Caught by my own scale-free scan, which reported `min L1_c/Ξ_c² = 0.2412453412` where
`½ − a/(2+a) = 0.3446` and `½ − 1/(4−a²) = 0.2412453412` — an exact match to the corrected
value.  Conclusion unchanged (`1/(4−a²) < ½ ⟺ a² < 2`), the reasoning corrected.

**F8. Theta-mode diagonal domination.**  `modeLam_diag : modeLam n n = 0` compiles, so the
diagonal carries `cos 0 = 1` and is sign-definite; but domination of the off-diagonal fails
(batch-9 numerics, negative lobe within a factor ≈6 at `x = 14.134725`).  Not re-run.

**F9. Integration by parts from `Φ = ψ″ − ψ/4` gives the factorisation, not the sign.**
The two derivatives act on the pair `(cosh(yt)cos(xt), sinh(yt)sin(xt))` exactly as
multiplication by `z² = (y+ix)²`, so `M(z) = (z²−¼)N(z)` — which is the elementary factor
`s(s−1)`, i.e. F4.  It relocates the difficulty to `N = π^{−s/2}Γ(s/2)ζ(s)` and does not
resolve it.

**F10. Compiler failures encountered (all repaired).**  `Complex.pow_re` does not exist
(use `pow_two` + `Complex.mul_re`); numerals `(2 : ℂ)` do not reduce under the `Complex.*_re`
simp set (write `z + z`); `nlinarith` fails on `2y·A·n < 0` with `A < 0` (use
`mul_neg_of_neg_of_pos ∘ mul_neg_of_pos_of_neg`).

---

## NUMERICAL (nonrigorous controls, explicit error bars)

Scripts: `tmp/c3b12_num.py → tmp/c3b12_num_out.txt`, `tmp/c3b12_num2.py → tmp/c3b12_num2_out.txt`.
Both exit 0.  Every quantity computed at two independent resolutions or by two routes.

**P1 — `momentTwo_eq` against direct 2D quadrature** (moments at 2000 vs 4000 nodes; direct at
`200×1500` vs `400×3000`):
```
  x=    0.000000  moments= 5.709915417228e-03 (self-err 4.32e-15)
                  direct = 5.709915417221e-03 (self-err 1.56e-16)   MISMATCH=6.493e-15
  x=   14.134725  moments= 9.559560388027e-07 (self-err 5.37e-16)
                  direct = 9.559560395466e-07 (self-err 1.59e-19)   MISMATCH=7.439e-16
```

**P2 — the readout dictionary** `c₀ = Ξ`, `s₁ = −Ξ′`, `c₂ = −Ξ″`, quadrature vs mpmath,
agreement `|d| ≤ 1.9e-12` (the quadrature's absolute floor) at six ordinates.

**P3 — `elementary_factor_split`**, `rel err ≤ 1.4e-28` at eight `(y,x)`.  Sign table:
```
     y     x   |z|^2-1/4      elem term         G term            sum
 0.100 0.100    -0.23000  -7.229213e-01   7.274894e-01   4.568079e-03
 0.490 0.050    -0.00740  -2.836998e+00   2.859619e+00   2.262147e-02
 0.600 0.200     0.15000   2.889333e+00  -2.861528e+00   2.780510e-02
 1.000 2.000     4.75000   3.078578e-01  -2.673668e-01   4.049103e-02
```

**P4 — hostile scan of the sub-leaf `L₁` to `x = 300`** (mpmath 30 dps; 601 points at step
0.5 plus 30 zero ordinates at `±0.01`): **0 negatives**, `min L1 = 1.246110e-194` at `x = 300`.
Zero fibre, matching the compiled `momentTwo_eq_sq_of_cosMom_zero`:
```
    x=14.134725142  L1=7.6476483164e-06  Xi'^2=7.6476483140e-06  |d|=2.35e-15
    x=25.010857580  L1=6.4029615208e-12  Xi'^2=6.4029615219e-12  |d|=1.09e-21
```

**P5′/P6 — the separation.**  `Φ_c`: 0 negatives on 2001 points, `min L1_c/Ξ_c² = 0.2412453412`
matching the corrected closed form `½ − 1/(4−e^{−2})` exactly.  `Φ_g`: 57/1201 negatives,
`min L1_g = −1.559942194e-02` at `x = 3.25`.
**`Φ_c` violates the leaf and satisfies the sub-leaf; `Φ_g` violates both.**

No mathematical route is declared successful on numerical grounds.

---

## PAPER_CHART_AUDIT

Read: `hp_pencil_v2.tex` in full (634 lines); `hp_pencil.tex` is the **superseded v1** (1982
lines, same programme, `_v2` is the current one and is what I cite);
`universal.tex` structure map plus every chart-bearing section read in full
(1–2050, 2438–3157, 3300–3640); `grh_companion.tex` overview and chart sections
(58–530, 560–960).  Sections of `universal.tex` I did **not** read line-by-line: the
Part II/III functoriality material (4211–5400, 5698–8004) and the appendices — none of them
introduces a chart, and I say so rather than implying full coverage.

| chart | exact references | preserved how in batch 12 |
|---|---|---|
| **native helix `Re s > 0`, phasors entering at 0** | `universal.tex` L1766–1782 (`thm:g7-readout-identity`: "enters at zero magnitude … the readout continues past the 1D line `Re s = 1`; that line is where the projected series stops converging in the readout chart, not a threshold on the carrier"); L1968–1988 (`lem:g9-fiber-growth`); abstract L106–111; `grh_companion` L150 | No convergence abscissa is invoked anywhere in `c3b12_A1/A2/A3`. `kM2_integrable` is proved by *tilt-shifting* (`t² ≤ 4(e^t+e^{−t})`), never by a half-plane. |
| **double helix / anti-helix conjugacy** | `universal.tex` L585–700 (`thm:g1-double-carrier`, `Γ_{H,±}` with phases `±Θ_H`, `J²=id` at L662–670); glossary L480; `thm:g8-reflected-completed-readout` L1815–1865; `grh_companion` L560–574, L862–901 | `C3B12.antihelix_swap` compiles the `p ↔ u` exchange and shows the carrier product is **invariant**, so the conjugate branch *equals* the helix branch. Recorded as F3. |
| **carrier `Z`, `t = log Z`** | `universal.tex` L109–111 ("physical height `Z>0` … analytic ordinate `y = log Z`"); L812–820 (`Π^log_21 := log z`, `Rec^log`); L2874–2875 (`Z = exp(Im ρ)`); L3357 (`heightReadout(e^γ)=γ`); `grh_companion` L174–181, L939 | All batch-12 work is on the carrier variable `u` (cell centre) and `p` (half-gap), i.e. the `t = log Z` chart. `momentTwo_eq` is a statement about `∫_{(0,∞)} u²·(…) du` — carrier-native. |
| **carrier-registration `S(t)` gap** | `universal.tex` §2438–3941; `thm:carrier-scale-S` L2485–2509 (`N_{π/3}(e^t) − R_1(e^t) = S_ev(t)`); typing convention L2454–2477; `S_Γ` contour coordinate L2589–2636 (**distinct object**); `S_{H,K}` cocycle L3559–3580; `thm:harmonic-family-S` L3582–3608 | **Not used and not blended.** Batch 12 touches no counting ledger. The three `S`s of the corpus — carrier `S_ev` (registration gap), contour `S_Γ` (path lift, L2609), classical `S_class` (strip census, L2468) — remain distinct; none is the pencil-side `S_t` of `hp_pencil_v2`. |
| **harmonisation `π/3`, not unit-1** | `universal.tex` L1393–1436 (`thm:g5-native-cell-closure`: `Δ=π/M ⟹ μ_{2M}`; `π/3` sharpest `= μ₆ = ℤ[ζ₆]`); L2446–2452; `rem:which-harmonic` L2511–2536; L3534–3541 (`pi3_arcs_eq`: marks at `k ≡ 3 mod 6`; `unit_arcs_empty`); L3550–3557 (`lattice_gap_fundamental`) | No batch-12 scan is a unit-1 cell scan. All numerics are **moment evaluations**, not cell-registration scans, so the `π/3` register is not at risk. Flagged: any future scan over a *cell* variable must be on `π/3` cells. |
| **Ξ chart `z = i(s−½)`** | `RequestProject/XiStructureFunction.lean:47` (`xiStructure z = ξ(½ − iz) + ξ′(½ − iz)`), `:101` (`chart_im : (I*(ρ−½)).im = ρ.re − ½`); `universal.tex` L3103–3113 (`(½+iz) − ρ = i(z − poleParam ρ)`) | **Two conjugate Ξ charts are in play and must not be merged**: `hp_pencil_v2` §1 L57 uses `A(z) := ξ(½+iz)` with `z_ρ = −i(ρ−½)`; `XiStructureFunction` uses `ξ(½−iz)` with `z = i(ρ−½)`. Batch 12 uses **neither** — it works in the carrier variable `z = y+ix` with `M(z) = 2ξ(½+z)`, a *third* chart, named explicitly in the EQUIV section only. |
| **HP pencil chart** | `hp_pencil_v2.tex` L73–86 (`μ_k(W)`, `H_n`, `H_n^{(1)}`), L99–111 (inertia), L208–227 (`prop:stieltjes`, quotient chart `w = z²`), L508–513 (`hyp:psd`), L538–592 (seat) | Batch 12 relates to it only through `C3B12.oddMoment_full_zero`, which shows this engine cannot supply the pencil's odd moments (F2). No pencil object is constructed or claimed. |
| **GRH family charts** | `grh_companion.tex` L99–104 (`π/3` carrier + Dirichlet fibre), L174–181 (`σ_*`, `carrierPointAtHeight(Z) = σ_* + i log Z`), L224 (`specBchan(γ,s) = γ + i(s−σ_*)`), L405 (`⟺ L(ρ,χ)=0 ∧ Re ρ = σ_*`), L414 (`N_{π/3}(e^t) − N_1(e^t) = S(t)`) | **SCOPE-CORRECTED (adjudication item 1).** `C3B12.gen_target_eq` is **restricted to real-valued even kernels** `W : ℝ → ℝ` with `W(−t) = W(t)` and four real integrable tilts. It does **not** apply verbatim to any Dirichlet/automorphic kernel: a **complex** character's kernel is complex-valued and obeys a root-number/conjugation law, not `hev`. Three prerequisites are **missing from this repository**: (i) a **complex-kernel pairing theorem** (`carrier_pairing2` re-proved for `ℝ → ℂ` with `conj` in the correct slot, since the `χ`/`χ̄` pairing gives `M·conj M`, not a square); (ii) the compiled **root-number / conjugation law** `W_χ(−t) = ε(χ)·W_{χ̄}(t)` replacing `hev`; (iii) a **per-character integrability bridge** (batch 10's Gaussian majorant is proved for `riemannXiKernel` alone). Covered with no new work: the trivial character and any **real (quadratic)** character's kernel, once evenness and the four integrabilities are supplied. **No GRH statement follows.** The `σ_*` midpoint is **not** used — batch 12 never places anything on a line. |

No paper edit is proposed: `grep -i "cellDensity|cell density|Laguerre|sinh(2yu)"` over all four
`.tex` files returns no hits, so the C3 campaign is still not in print and nothing here changes
a printed claim.

---

## GIT REVIEW

```
git diff --stat                       →  EMPTY (no tracked file modified)
git status --porcelain | grep -v '^?? tmp/'
?? RequestProject/WeightedTailPrimitive.lean      (pre-existing, untouched)
?? RequestProject/WeightedTailSinhBridge.lean     (pre-existing, untouched, still unbuilt)
?? RequestProject/XiHelixChart.lean               (pre-existing, untouched)
?? RequestProject/XiStructureResidual634.lean     (pre-existing, untouched)
?? RequestProject/XiStructureSeatBridge.lean      (pre-existing, untouched)
```
New this batch, all untracked, all under `tmp/`, nothing committed:
`c3b12_A1.lean/.olean`, `c3b12_A2.lean/.log/.olean`, `c3b12_A3.lean/.olean`,
`c3b12_num.py`, `c3b12_num_out.txt`, `c3b12_num2.py`, `c3b12_num2_out.txt`,
`claude_c3_proof_batch12_20260825.md`.
Modified in place (batch-11 corrections only, as instructed):
`claude_c3_proof_batch11_20260825.md`, `c3b11_num2.py`.
`tmp/c3b10_A1..A3.lean` and `tmp/c3b11_A1..A3.lean`: **not opened for write**.

---

## MACHINE-READABLE SUMMARY

```yaml
batch: c3-batch-12
date: 2026-08-25
target_proved: false
rh_claimed: false
grh_claimed: false
commits: 0
tracked_files_modified: 0
lean_files_new: 3
declarations_compiled: 44
declarations_by_file: {A1: 19, A2: 17, A3: 8}
axiom_footprint_all: "[propext, Classical.choice, Quot.sound]"
compilation_provenance: "A1 compiled by me (exit 0); A2 and A3 compiled INDEPENDENTLY by the OpenAI adjudicator after the corrections (exit 0, all declarations at the standard footprint)"
forbidden_pattern_scan: "clean (exit 1, no output) over A1/A2/A3, re-run by the adjudicator on the corrected files"
attacks_executed: 20
headline:
  name: C3B12.momentTwo_eq
  statement: "int_{Ioi 0} u^2 * cellDensity x u = 8^{-1}*(cosMom Phi x * cosMom kM2 x + sinMom kM1 x ^2)"
  hypotheses: none
  reading: "= (1/8)(Xi'(x)^2 - Xi(x)Xi''(x)): the even moments of the cell density ARE the Laguerre expressions of the readout"
new_unconditional_fibres:
  - "C3B12.momentTwo_eq_sq_of_cosMom_zero: at every real zero of the readout the second moment is a perfect square (1/8)Xi'^2"
  - "C3B12.cellDensity_Ioi_eq_sq: the first tail is ONE square, not two"
  - "C3B12.momentTwo_zero_nonneg: the x=0 fibre of the second moment"
generalization:
  name: C3B12.gen_target_eq
  content: "the batch-11 leaf identity holds for real-valued even measurable kernels with the four tilts integrable; complex characters additionally require a complex-kernel pairing theorem, a root-number/conjugation law, and a per-character integrability bridge"
separation_result:
  Phi_c: "e^{-t^2}(2+cos 2t): VIOLATES full leaf, SATISFIES u^2 sub-leaf (exact: L1_c = Xi_c^2(1/2 - h), max h = 1/(4-e^{-2}) < 1/2)"
  Phi_g: "e^{-t^2}+e^{-4t^2}: VIOLATES full leaf, VIOLATES u^2 sub-leaf (min -1.5599e-02 at x=3.25)"
  consequence: "the u^2 sub-leaf is STRICTLY WEAKER than the leaf, so the batch-11 counterexample does not obstruct it; but it is still not implied by evenness+positivity"
open_next_lean_statement: |
  theorem laguerre_edge (x : R) :
      0 <= C3B10.cosMom riemannXiKernel x * C3B10.cosMom C3B12.kM2 x
        + C3B10.sinMom C3B12.kM1 x ^ 2
open_smallest_subfibre: "full inequality cosMom Phi x * cosMom kM2 x + sinMom kM1 x ^ 2 >= 0; product-sign-only route is FAILED F11"
hostile_scans:
  sub_leaf_L1: {range: "x in [0,300] step 0.5 + 30 zero ordinates", points: 691, negatives: 0, min: 1.246110e-194, certified: false, note: "high-precision-cross-checked numerical evidence only"}
retractions_this_batch:
  - "batch-11 factor 2 in Q/|M|^2 (corrected in place)"
  - "batch-11 whole-class Gaussian-mixture claim (withdrawn, restricted to the example)"
  - "my own c3b12_num.py P5 finite-difference negatives: roundoff, redone in closed form -> 0 negatives"
  - "my own pencil claim that h(c) maximises at c=1: wrong, max is at c*=(2-a^2)/a, value 1/(4-a^2); conclusion unchanged"
  - "my own printed 'outside the disc both terms are positive': refuted by my own table (the G term is negative there)"
literature_check_still_required:
  - "first Laguerre inequality Xi'^2 - Xi Xi'' >= 0 for the Riemann Xi function: NOT read at source (no web access, two sessions running)"
```
