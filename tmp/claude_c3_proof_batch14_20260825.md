# C3 proof batch 14 — the normal form is COMPILED, and the routes into it are enumerated and killed

Date 2026-08-25.  `/Users/samuellavery/work/helix_frobenius`, branch `ladder-campaign-2026-08`.
**No commit.  `git diff --stat` EMPTY — no tracked file modified.  All new files are
`tmp/c3b14_*`.**  `AGENTS.md` still does not exist in this repository.  `CLAUDE.md` obeyed.

**HEADLINE.**  Batch 13's "smallest next Lean theorem" is **proved**, and with it the target's
normal form.  23 new declarations, all axiom-clean:

> `C3B14.cosMom_Rker (x : ℝ) :`
> `cosMom Rker (2*x) = 4⁻¹ * (cosMom Φ x * cosMom kM2 x + sinMom kM1 x ^ 2)`
> with `Rker v = ∫ p², Φ(v+p)Φ(v−p) dp`, proved `≥ 0` pointwise, even, and integrable.

So the first Laguerre inequality for `Ξ` **is exactly the statement that one explicit
nonnegative even function is positive definite** (`target_iff_cosMom_Rker_nonneg`, compiled).
The batch then attacks that normal form 24 ways and **kills every classical route into it**,
including three of its own intermediate findings.

---

## 0. CORRECTIONS APPLIED TO BATCH 13 BEFORE NEW WORK

All four adjudication items were applied to `tmp/claude_c3_proof_batch13_20260825.md` and to
the Lean **docstrings** (`c3b13_A1.lean`, `c3b13_A4.lean`, `c3b13_A5.lean`).  **No theorem
statement was changed**; all 49 batch-13 declarations recompile at
`[propext, Classical.choice, Quot.sound]`.

| # | correction |
|---|---|
| 1 | `momentTwo_nonneg_of_thickened` / `momentTwo_nonneg_of_large_readout` are **compiled conditional criteria** — unconditional implications whose real-inequality hypotheses are **not proved to hold at any `x`**. "Unconditional fibre" removed throughout. |
| 2 | The "interval around each real zero" reading additionally needs **continuity** of `x ↦ cosMom Φ x`, `x ↦ sinMom kM1 x` **and `Ξ′(γ) ≠ 0`**; neither formalised, so it is **numerical/unformalised**. |
| 3 | Small-readout and large-readout are **oppositely directed but not logical complements**; they do **not** partition the line. Measured union 4.41%, so **95.59% satisfies neither**. `momentTwo_nonneg_of_either` is a disjunction, not a dichotomy. |
| 4 | "load-bearing" removed; the Jacobi reflection is now described neutrally (`Φ` is even as an identity; an even differentiable function has vanishing derivative at 0, so the corner mechanism does not apply). |

**A FIFTH DEFECT, found by this batch's own audit and corrected in batch 13 in place.**
Batch 13's **F4** killed the Schoenberg route by asserting "`|L₁|` is not monotone (§P11)".
That evidence (a) **did not exist** — §P11's number came from `tmp/c3b13_num2.py`, which never
finished, as batch 13's own ledger states two sections later — and (b) is **false**:
recomputed cancellation-free at 40 digits (`tmp/c3b14_num3_out.txt`), `|L₁|` increases at
**0/80** steps on `[0,20]`, **0/240** on `[0,60]`, **0/240** on `[0,120]`.  F4's *conclusion*
survives on new, direct evidence (§S2 below); its stated evidence is retracted.  §P11 is
marked RETRACTED and may not be cited.

---

## COMPILED

Commands, literal:

```
env LEAN_PATH=tmp lake env lean tmp/c3b14_A1.lean
env LEAN_PATH=tmp lake env lean -o tmp/c3b14_A1.olean tmp/c3b14_A1.lean
env LEAN_PATH=tmp lake env lean tmp/c3b14_A2.lean
```

Audit log `tmp/c3b14_audit.log`: **23 lines, 23/23 exactly
`[propext, Classical.choice, Quot.sound]`**, `grep -c "error\|sorryAx"` → **0**.
Escape scan over both files → **exit 1, no output**.

### `tmp/c3b14_A1.lean` — the convolution pairing (10 decls)

```lean
theorem carrier_conv_pairing (hIA : Integrable A) (hmA : Measurable A)
    (hIB : Integrable B) (hmB : Measurable B) (x : ℝ) :
    (∫ v : ℝ, (∫ p : ℝ, A (v + p) * B (v - p)) * Real.cos (x * v))
      = 2⁻¹ * (cosMom A (x / 2) * cosMom B (x / 2)
          - sinMom A (x / 2) * sinMom B (x / 2))

theorem carrier_conv_pairing_integrable ... : Integrable (fun v => (∫ p, A (v+p) * B (v-p)) * Real.cos (x * v))
```

The companion of `C3B11.carrier_pairing2` with the chart clock moved from the **half-gap** to
the **cell centre**.  Two things change, and **both were audited numerically before the file
was written** (`tmp/c3b14_num1_out.txt` Part I, on kernels with *no* symmetry so all four
moment slots are exercised):

* the moments are read at **`x/2`**, not `x`;
* the channels combine with a **MINUS**, not the plus of `carrier_pairing2`.

The audit prints the plus form alongside; it is wrong at every `x ≠ 0`
(`0.73871` vs `0.94906` at `x = 1.3`).  Worst relative error of the minus form: **`4.6e-15`**.

Mechanism of the sign, in one line: after the shear `(v,p) ↦ (v+p, p)` and the dilation
`q = 2p`, the clock becomes `cos(x(t+t′)/2)` on the **sum** of the leg variables, and `cos` of
a sum carries the minus; `carrier_pairing2`'s clock lands on the **difference**.

### `tmp/c3b14_A2.lean` — the `R` kernel and the exact identity (13 decls)

```lean
def Rker (v : ℝ) : ℝ := ∫ p : ℝ, p ^ 2 * (riemannXiKernel (v + p) * riemannXiKernel (v - p))

theorem Rker_nonneg (v : ℝ) : 0 ≤ Rker v            -- three nonnegative factors
theorem Rker_even (v : ℝ) : Rker (-v) = Rker v       -- from riemannXiKernel_neg; legs exchange
theorem Rker_integrable : Integrable Rker            -- NOT the zero-convention

theorem cosMom_Rker (x : ℝ) :                        -- hypotheses: NONE
    cosMom Rker (2 * x)
      = 4⁻¹ * (cosMom riemannXiKernel x * cosMom kM2 x + sinMom kM1 x ^ 2)

theorem cosMom_Rker_eq_two_momentTwo (x : ℝ) :
    cosMom Rker (2 * x) = 2 * ∫ u in Ioi (0 : ℝ), u ^ 2 * cellDensity x u

theorem target_iff_cosMom_Rker_nonneg (x : ℝ) :
    (0 ≤ cosMom riemannXiKernel x * cosMom kM2 x + sinMom kM1 x ^ 2)
      ↔ 0 ≤ cosMom Rker (2 * x)
```

**How the square survives a formula made only of minuses.**  Transposing batch 12's centre
split to the gap, `4p² = ((v+p) − (v−p))²` puts a **minus** on the cross term; the pairing
contributes its own **minus** between channels; and parity (`cosMom kM1 = 0`) leaves
`−2·½(0 − s₁²) = +s₁²`.  The two minuses multiply.

`Rker_integrable` matters: without it `cosMom Rker` could be Lean's zero-convention value on
a non-integrable function, and the identity would carry no analytic content.  It is derived
from the three legs through `carrier_conv_pairing_integrable`.

**Factor audit, run before formalisation** (`tmp/c3b14_num1_out.txt` Part II): the `¼` form
matches direct quadrature to **`5.9e-16`** at six ordinates; the competing `½` and `⅛` forms
are printed alongside and are wrong by exactly a factor 2.  `R ≥ 0` and `R` even were checked
on the same grid (`max |R(v) − R(−v)| = 6.2e-17`), and `cosMom R 0 = 0.01141983083444`
reproduces batch 13's `L₁(0)` to 14 digits.

**Free consequences.** `cosMom_Rker_zero_nonneg` recovers `C3B12.momentTwo_zero_nonneg` from
`R ≥ 0` with no positivity computation; `cosMom_Rker_abs_le` re-derives batch 13's sharp
constant `|L₁(x)| ≤ L₁(0)` as the one-line `|∫R cos| ≤ ∫R` — an **independent second route**
to a constant batch 13 obtained by cell-density domination.

---

## OPEN

```lean
theorem laguerre_edge (x : ℝ) : 0 ≤ C3B14.cosMom Rker (2 * x)
```

equivalently (compiled `iff`) the batch-12 bracket.  **Nothing was removed from the open
region this batch**: `target_iff_cosMom_Rker_nonneg` is an equivalence, and every route into
it tested below is dead.  What changed is the *shape* of the question — from a signed
integral to the positive-definiteness of an exhibited nonnegative function — and the
enumeration of which classical criteria can and cannot apply to it.

---

## EQUIV — navigation only

* **Target ⟺ `R` positive definite** (`target_iff_cosMom_Rker_nonneg`, COMPILED). This is the
  normal form; it is an EQUIV and is labelled as one.
* **`cosMom R (2x) = 2·∫_{(0,∞)}u²C(x,u)du`** (COMPILED) — the bridge to batch 12's engine.
* **`R(v) = (M₂∗Φ)(2v) − v²(Φ∗Φ)(2v)`** — exact (checked to `5.5e-13`, §S4). The `k = 0`
  analogue `R₀(v) = ½(Φ∗Φ)(2v)` **is** a convolution square, which is why its transform is
  `Ξ²  ≥ 0`; the `−v²` term is precisely what destroys that structure at `k = 1`.
* Batch 13's EQUIVs (Hadamard sum, `∂²_σ|ξ|²`, log-concavity of `|Ξ|` between zeros) unchanged.

---

## FAILED — 24 attacks, and every classical route into the normal form

Necessary conditions are tested first: a failure there would refute the **TARGET**, not a
route.  All three hold, so the conjecture survives its own adversarial tests.

### Necessary conditions (tests of the conjecture itself) — ALL HOLD

**N1. A positive-definite function attains its maximum at 0.**  `max R = R(0) = 0.031438117`
on `[0,3.4]`, attained at `v = 0`.  HOLDS.

**N2. Bochner, finite form.**  `[R(vᵢ − vⱼ)]` must be PSD for every finite point set. Seven
hostile sets (uniform at `h = 0.05/0.20/0.50`, clustered near 0, wide `h = 1.0`, a
deterministic golden-ratio ragged set, two separated clusters):

```
     uniform h=0.05, n=40       min eigenvalue =  2.433477e-14  ok
     clustered near 0, n=30     min eigenvalue = -2.721315e-17  ok
     ragged (golden), n=35      min eigenvalue =  7.704376e-07  ok
     two clusters, n=24         min eigenvalue =  3.352358e-15  ok
```
Worst `−2.7e-17`, at numerical zero.  HOLDS.

**N3. Hamburger moments.**  If `R̂ ≥ 0` then `m_k = ∫ξ^{2k}R̂dξ` is a moment sequence of a
positive measure, so `[m_{i+j}]` must be PSD.  Control fired: `m₀ = 1.975315151551e−01`
against `2πR(0) = 1.975315151551e−01` (`reldiff 1.5e-14`).  Hankel eigenvalues
`2×2: [1.31e−01, 1.29e+03]`, `3×3: [1.05e−01, 3.67e+02, 9.47e+07]`.  HOLDS.

**N4. Hostile transform scan.**  `ξ ∈ [0,100]` step `0.05`: **0 negatives** on the
informative window `ξ ≤ 20`.  Beyond that `R̂(ξ) ∼ e^{−πξ/4}` drops under the float64
quadrature floor and the signs there are **not informative** — stated, not hidden.

### Sufficient conditions — all dead

**F1. Pólya, and every corner-generated class — dead by a proof, not a measurement.**  A
convex decreasing `R` on `(0,∞)` with `R′(0⁺) = 0` forces `R` constant.  `R` is even and
smooth, so `R′(0⁺) = 0`.  **Pólya's criterion cannot apply to any smooth even kernel.**  The
same argument kills every mixture of PD generators having a corner at 0 — in particular every
`∫e^{−λ|v|}dμ(λ)` representation, whose one-sided derivative at 0 is `−∫λ dμ < 0` unless
`μ = 0`.  Measured consistency: `R` is decreasing on `(0,∞)` (True) and **not** convex there.

**F2. Bernstein / Stieltjes / complete monotonicity in `|v|` — dead by the same proof.**  A
completely monotone function of `|v|` is exactly such a mixture.  Structural, not measured.

**F3. Schoenberg / Gaussian scale mixture — dead, and this is the corrected kill for batch
13's F4.**  `R` is a Gaussian scale mixture iff `g(τ) := R(√τ)` is completely monotone.
Measured: `(−1)¹g′ ≥ 0`, `(−1)²g″ ≥ 0`, but

```
     (-1)^3 g^(3): min = -3.812438e+00   NEGATIVE -> not CM
     (-1)^4 g^(4): min = -2.554617e+04   NEGATIVE -> not CM
```

Complete monotonicity fails at the **third** derivative.  Route dead.  (Batch 13 reached the
same conclusion from a claim about monotonicity of `|L₁|` that was both uncited and false;
see §0.)

**F4. Total positivity / Pólya-frequency / determinantal — dead because it does not IMPLY the
conclusion.**  TP2 for `K(a,b) = R(a−b)` is equivalent to log-concavity of `R`.  Measured
(§D3, off the underflow region): `R` **is** log-concave on `[0,0.75]`, `(log R)″ ∈ [−114,−47]`.
But log-concavity gives nothing:

> `W(v) = e^{−v⁴}` is even, positive and log-concave (`(log W)″ = −12v² ≤ 0`), and
> `e^{−|v|^p}` is positive definite only for `p ≤ 2`.  **Measured: its transform has
> `min = −1.872725e−01` at `ξ = 4.600`.**

And `TP_∞` (Pólya frequency) would force, by Schoenberg, `R̂ = 1/Ψ` with `Ψ` in
Laguerre–Pólya — a zero-freeness statement about `R̂`, which is neither what is wanted nor
available.  The whole determinantal family is dead for a *reason*, not by measurement of its
hypotheses.

**F5. Variation diminishing — dead, downstream of F4.**  `R` has 0 sign changes and `R̂` has
0 on `ξ ≤ 20`, so a VD argument *would* deliver the target — but VD is a property of totally
positive kernels, and F4 removes that.

**F6. Fourier convolution square — no sign available.**  `R = h⋆h` ⟺ `R̂ ≥ 0` is circular.
The non-circular content is the exact decomposition `R(v) = (M₂∗Φ)(2v) − v²(Φ∗Φ)(2v)`
(verified to `5.5e-13`): the `k = 0` analogue is a genuine convolution square and that is why
its transform is `Ξ²`; the `−v²` term destroys the structure at `k = 1`.

**F7. Antihelix conjugation gives nothing here, and the reason is compiled.**  The swap
`v ↔ p` sends `R` to `∫v²Φ(p+v)Φ(p−v)dv`, and by `C3B12.antihelix_swap` the carrier product
is invariant, so this is the *same* bilinear form read on the other axis (measured
`reldiff 0.00e+00`).  Consistent with batch 12's F3.

**F8. Heat / de Bruijn flow on `R` — PRE-REGISTERED prediction, and it was WRONG.**  I
pre-registered: `λ > 0` keeps `R̂_λ ≥ 0`; `λ < 0` **eventually produces a negative**.
Measured over `λ ∈ {0.25, 0.1, 0, −0.05, −0.1, −0.2, −0.35}`, `ξ ≤ 20`: **0 negatives at every
`λ`**, and the minimum *increases* monotonically as `λ` decreases
(`1.481e−04 → 1.602e−04`).  Backward flow did not break the sign in this window.  The
prediction is retracted; the flow supplies no instrument either way.

**F9. Symmetrized theta terms — batch 13's refutation spec RS-1, run here at this batch's
instruction, and MY PREDICTION WAS REFUTED.**  RS-1 predicted that the corner-free
symmetrisations `S_k(u) = φ_k(u) + φ_k(−u)` would be **nonnegative** and satisfy the target.
Measured:

```
   k      min S_k on [-4,4]     at u   S_k >= 0 ?
   1      -1.5672622648e+00   -0.833        False
   2      -1.1083523155e+00   -1.526        False
   3      -9.0496567155e-01   -1.931        False
```

`φ_k(u) < 0` for `u < ½log(3/(2πk²))` — the second theta term dominates at large negative `u`
— so a symmetrised **single term is not a positive kernel at all**.  The termwise route dies,
but for a reason I did not anticipate: not that the pieces fail the target, but that they are
**not admissible positive kernels**.  RS-1 is answered, by me, against my own prediction.

**F10. Compactly supported approximation — no negatives, and my stated reading was wrong.**
Hard cutoffs `T ∈ {0.5,1,1.5,2,3}` give **0 negatives** on `ξ ≤ 20`.  My script's prose
predicted a jump artefact would oscillate the sign; it did not appear in this window, and the
prediction is withdrawn.  (For `T ≥ 1.5` the truncation is numerically inert — `Φ` is already
negligible there.)

**F11. `π/3` harmonisation is NOT APPLICABLE here, and is reported as a null by design.**  The
`π/3` register governs cell-**registration counts** `N_{π/3}(e^t) − N_1(e^t)`.  `R`'s argument
`v` is a cell **centre** in a moment integral; no count is formed anywhere in this batch.
Forcing a unit-1 cell scan would be the documented false-null trap, so none was run.  Sanity
only: `R(kπ/3)/R(0) = 1.28e−16, 1.37e−171, 0` for `k = 1,2,3` — no structure, as expected.

### Three defects of my OWN blocks, caught by this batch's adjudication (§`c3b14_num5`)

**F12. WITHDRAWN: "the Gaussian violates the target".**  Block 4's transfer table reported
`exp(−t²)` with "57 negatives, min `−2.67e−12`" and `Φ_c` with 25.  **Both false.**  For
`W = e^{−t²}` everything is closed form: `R(v) = ¼√(π/2)e^{−2v²}`, `R̂(ξ) = (π/8)e^{−ξ²/8} > 0`
**strictly** — verified against `¼(c₀c₂+s₁²)` to 14 digits at five ordinates.  The
"negatives" were the truncation floor of a `v`-grid built for `Φ` (doubly exponential decay)
and reused for kernels with far heavier tails.  Rerun with per-kernel grids: Gaussian
`min = −2.2e−17` (noise), `Φ_c` **positive**, `min = +1.2e−15`.

**F13. WITHDRAWN: block 4's printed verdict "TP is FALSE for this kernel".**  Its own table
showed **0/5** TP2 violations, all minors positive.  The printed conclusion contradicted the
data.  Replaced by F4's structural argument, which needs no minors.  (Same defect class as
batch 12's "outside the disc both are positive".)

**F14. WITHDRAWN: block 2's "`(log R)″` max = `+7.49e5`, `R` not log-concave".**  That maximum
sits where `R` has underflowed to 0 and `log R` was clamped at `log(10⁻³⁰⁰)`.  Re-measured on
`[0,0.75]` where `R ∈ [3.14e−2, 5.07e−9]` is fully representable: `(log R)″ ∈ [−114, −47]`,
so **`R` IS log-concave** there.  (This *strengthens* the structure and still gives nothing,
by F4.)

---

## HOSTILE NUMERICS — the transfer battery, re-run with per-kernel grids

A row counts as a **real** violation only if `|min|` exceeds the kernel's own tail residual by
orders of magnitude and the location is stable.

```
                          kernel      PL,VMAX         min Rhat   at xi   neg     R(VMAX)      verdict
                   Phi (Riemann)      6.6,3.4       1.5314e-04   20.00     0    0.00e+00     positive
              exp(-t^2) Gaussian     14.0,8.0      -2.2146e-17   19.05    49    8.06e-57        noise
      exp(-t^2)+exp(-4t^2) Phi_g     14.0,8.0      -3.8999e-03    6.50    57    8.06e-57     REAL NEG
        exp(-t^2)(2+cos2t) Phi_c     14.0,8.0       1.2048e-15   20.00     0    3.40e-56     positive
             Phi + 0.5 exp(-t^2)     14.0,8.0      -1.7536e-02    5.40    86    2.01e-57     REAL NEG
                         sech(t)    30.0,18.0      -5.9513e-13   11.45   103    3.63e-12        noise
                       exp(-t^4)      8.0,5.0       1.4602e-05   20.00     0    0.00e+00     positive
```

**Two readings, both new.**

1. **`Φ_g`'s violation is confirmed independently and its location matches exactly.**  Batch
   12 found `min L₁_g` at `x = 3.25` by closed form; here the transform's minimum is at
   `ξ = 6.50 = 2·3.25`.  Two different computations, same point.
2. **The target is FRAGILE in kernel space, with a measurable threshold.**  `Φ + 0.05e^{−t²}`
   is positive (block 4); `Φ + 0.5e^{−t²}` is **really negative** (`−1.75e−02` at `ξ = 5.40`).
   So a modest, smooth, even, positive additive perturbation of the Riemann kernel destroys
   the target, and the threshold lies between `ε = 0.05` and `ε = 0.5`.  This is the sharpest
   available statement of how much room the conjecture has: **finite, but not large.**
   Locating the threshold is not attempted here and is not claimed.

Batch 13's hostile `L₁` scan (2144 points, `x ≤ 400`, 27 zero ordinates × 9 offsets,
0 negatives) stands unchanged and is not re-run.

---

## PAPER / CHART AUDIT — corrected

Read this batch: `tmp/c3b11_A1.lean` (the pairing template, in full), `tmp/c3b12_A1..A3.lean`,
`tmp/c3b13_A1..A5.lean`, batch 13's ledger in full, `RequestProject/XiStructureFunction.lean`,
`JKernelSignLaw.lean`, `ThetaWronskianSuzukiGram.lean:40-80`.  Batch 13's `universal.tex`
citations were spot-checked at source in that batch and were re-confirmed at L106–111,
L1766–1782, L2485–2492, L3534–3542; they are not re-quoted here.

| chart | preserved how in batch 14 |
|---|---|
| **native helix `Re s > 0`, phasors entering at 0** | No convergence abscissa is invoked in `c3b14_A1/A2`. Every integrability fact comes from `|cos| ≤ 1` plus batch 10/11 majorants; no half-plane appears anywhere. |
| **physical carrier `Z > 0`, `y = log Z`** | `Rker` is a function of the cell centre `v`, integrated against the half-gap `p` — both carrier variables in the `t = log Z` chart. `carrier_conv_pairing` is stated entirely in `(v,p)`. |
| **double helix / anti-helix conjugation** | Used, not merely cited: `C3B12.antihelix_swap` is what makes the `v ↔ p` swap send `R` to the same bilinear form (§F7, `reldiff 0.00e+00`), which is why the "dual" representation buys a normal form and not a new bound. |
| **`S(t) = N_{π/3}(e^t) − N_1(e^t)` as a REGISTRATION GAP, not a unit-1 cell scan** | **Not used and not blended.** No count is formed in this batch. §F11 records the applicability check explicitly and declines to run a cell scan, because a unit-1 scan is the documented false-null trap. The corrected reading is stated there: `v` is a cell *centre* in a moment integral, not a registration cell index. |
| **`Ξ` chart** | `Ξ(x) = ξ(½+ix)` throughout, with `cosMom riemannXiKernel x = 2Ξ(x)` (batch 13, `κ = 2` to `2.3e-61`). Kept distinct from `hp_pencil_v2`'s `A(z) = ξ(½+iz)` and from `XiStructureFunction`'s `ξ(½−iz)`; never merged. |
| **GRH family charts** | Untouched. `carrier_conv_pairing` is stated for real `A, B : ℝ → ℝ`; batch 12's three missing prerequisites for complex characters (complex-kernel pairing, root-number law, per-character integrability bridge) are all still missing. **No GRH statement follows from this batch.** |

The C3 campaign remains **not in print**; no paper edit is proposed.

---

## THE SMALLEST NEXT LEAN THEOREM

Every soft criterion is now dead (F1–F6), and batch 13 established that any proof must consume
arithmetic input.  The smallest statement that *supplies* such input to the compiled normal
form, rather than restating it, is the positive-definiteness of `R` **restricted to a compact
frequency window**, fed by the repo's existing zero-location facts.  The smallest well-posed
Lean step toward it is the window-truncation bound, which is pure analysis and needs no
arithmetic:

> ## ⚠ RETRACTED 2026-08-25 (OpenAI adjudication) — the statement below is FALSE
>
> The version printed in the first release of this ledger carried an **extra factor 2 on the
> central integral**:
> ```lean
> -- FALSE, DO NOT USE:
> theorem cosMom_Rker_window (a x : ℝ) (ha : 0 ≤ a) :
>     2 * (∫ v in Set.Ioo (-a) a, Rker v * Real.cos (2 * x * v))
>       - 2 * (∫ v in Set.Ioi a, Rker v) ≤ cosMom Rker (2 * x)
> ```
> **It fails already at `x = 0` for large `a`.**  Let `S := ∫_{(0,∞)}R`, so
> `cosMom Rker 0 = 2S`.  As `a → ∞` the printed left side tends to `2·(2S) − 0 = 4S` while
> the right side is `2S`, so the claim asserts `4S ≤ 2S`, i.e. `S ≤ 0` — false, since
> `2S = 0.011419830834 > 0` (measured, batch 13 §P1 and batch 14 §Part II).  The error is
> arithmetic, not numerical: the window and its complement **partition** the line, so the
> central piece enters with coefficient **1**, not 2.
>
> **Corrected statement** (compiled in batch 15 as `C3B15.window_lower_tail`):

```lean
theorem cosMom_Rker_window (a x : ℝ) (ha : 0 ≤ a) :
    (∫ v in Set.Ioo (-a) a, Rker v * Real.cos (2 * x * v))
      - 2 * (∫ v in Set.Ioi a, Rker v)
    ≤ cosMom Rker (2 * x)
```

i.e. the transform is bounded below by its truncation minus twice the tail mass — the exact
inequality that turns "`R` is positive definite" into a **finite, checkable** statement once a
tail bound on `R` is available.  `Rker_nonneg` and `Rker_integrable` are already compiled, so
the proof is a split plus `|cos| ≤ 1`; the arithmetic enters only afterwards, in bounding the
tail.  Stated honestly: this is a **reduction step**, not a discharge, and it is `STRONGER`-
shaped only in the sense that it exhibits an object (the window) rather than estimating one.

---

## MACHINE-READABLE SUMMARY

```yaml
batch: c3-batch-14
date: 2026-08-25
branch: ladder-campaign-2026-08
target_proved: false
rh_claimed: false
grh_claimed: false
novelty_claimed: false
commits: 0
tracked_files_modified: 0
agents_md_present: false
lean_files_new: 2
declarations_compiled: 23
declarations_by_file: {A1: 10, A2: 13}
axiom_footprint_all: "[propext, Classical.choice, Quot.sound]"
audit_log: tmp/c3b14_audit.log
forbidden_pattern_scan: "clean (exit 1, no output) over c3b14_A1, c3b14_A2"
batch13_corrections_applied: 5
batch13_recompiles_clean: true
attacks_executed: 24
headline:
  name: C3B14.cosMom_Rker
  statement: "cosMom Rker (2*x) = 4^{-1} * (cosMom Phi x * cosMom kM2 x + sinMom kM1 x ^ 2)"
  hypotheses: none
  reading: "the first Laguerre expression of the readout IS the cosine transform of the explicit nonnegative even function R(v) = int p^2 Phi(v+p)Phi(v-p) dp"
  factor_audit: "1/4 form matches direct quadrature to 5.9e-16; competing 1/2 and 1/8 printed and wrong by exactly 2x"
supporting:
  - "C3B14.carrier_conv_pairing: clock on the CELL CENTRE, moments at x/2, MINUS between channels (audited to 4.6e-15; PLUS form printed and visibly wrong)"
  - "C3B14.Rker_nonneg / Rker_even / Rker_integrable"
  - "C3B14.target_iff_cosMom_Rker_nonneg: the normal form, as an iff"
  - "C3B14.cosMom_Rker_abs_le: independent second route to batch 13's sharp constant |L1(x)| <= L1(0)"
necessary_conditions_all_hold:
  - "N1 max at 0; N2 Bochner Gram PSD on 7 hostile point sets, worst -2.7e-17; N3 Hamburger Hankel PSD with control m0 = 2 pi R(0) to 1.5e-14; N4 zero negatives on the informative window"
routes_killed:
  - "Polya and every corner-generated class: STRUCTURAL PROOF (smooth even => R'(0+)=0 => convex+decreasing forces constant)"
  - "Bernstein/Stieltjes/complete monotonicity in |v|: same structural proof"
  - "Schoenberg/Gaussian scale mixture: complete monotonicity of g(tau)=R(sqrt tau) fails at the THIRD derivative, min -3.81"
  - "Total positivity / Polya frequency / determinantal: TP2 == log-concavity, and log-concavity does NOT imply a nonneg transform (witness exp(-v^4), transform min -0.187)"
  - "Variation diminishing: downstream of TP"
  - "Fourier convolution square: R = (M2*Phi)(2v) - v^2 (Phi*Phi)(2v); the -v^2 term destroys the square"
  - "Antihelix conjugation: the swap gives the SAME bilinear form (antihelix_swap)"
retractions_this_batch:
  - "F12: my block-4 claim that the Gaussian exp(-t^2) violates the target (57 negatives). FALSE: Rhat = (pi/8)exp(-xi^2/8) > 0 in closed form; the negatives were truncation floor. Phi_c likewise; rerun gives POSITIVE."
  - "F13: my block-4 printed verdict 'TP is FALSE' contradicted its own table (0/5 violations). Withdrawn; replaced by a structural argument."
  - "F14: my block-2 claim that R is not log-concave. The +7.49e5 maximum was in the underflow region. R IS log-concave on [0,0.75]."
  - "F8: my PRE-REGISTERED prediction that backward de Bruijn flow (lam<0) would produce a negative. It did not: 0 negatives at every lam tested, and the minimum INCREASES as lam decreases."
  - "F9: my batch-13 refutation spec RS-1 prediction that symmetrized theta terms S_k are nonnegative. REFUTED: min S_1 = -1.567. They are not positive kernels at all."
  - "F10: my prediction that compact truncation would oscillate the sign via a jump artefact. 0 negatives observed."
  - "batch 13 F4/P11 (corrected in place): cited a script that never ran, and asserted non-monotonicity of |L1| which is FALSE on [0,120] (0 increases at step 0.25, 40 digits)."
new_finding_fragility:
  content: "the target is FRAGILE in kernel space with a measurable threshold: Phi + 0.05 exp(-t^2) is positive, Phi + 0.5 exp(-t^2) is REALLY negative (min -1.75e-02 at xi=5.40). Threshold between eps=0.05 and eps=0.5; not located, not claimed."
  independent_confirmation: "Phi_g's violation location xi = 6.50 matches batch 12's closed-form x = 3.25 exactly (xi = 2x)"
literature_check_still_required:
  - "first Laguerre inequality for the Riemann Xi function: NOT read at source (web tools unavailable, FOUR sessions running). NO novelty is claimed anywhere."
open_next_lean_statement: |
  theorem cosMom_Rker_window (a x : R) (ha : 0 <= a) :
      (int v in Set.Ioo (-a) a, Rker v * Real.cos (2*x*v)) - 2 * (int v in Set.Ioi a, Rker v)
        <= cosMom Rker (2*x)
  # NOTE: the first release of this ledger printed an extra factor 2 on the central
  # integral.  That version is FALSE (it fails at x=0 as a -> infinity, asserting S <= 0
  # for S = 0.00571 > 0) and is RETRACTED.  Coefficient on the central piece is 1.
open_next_purpose: "turns 'R is positive definite' into a finite checkable statement once a tail bound on R is available; pure analysis, arithmetic enters only afterwards in bounding the tail. A reduction step, not a discharge."
```
