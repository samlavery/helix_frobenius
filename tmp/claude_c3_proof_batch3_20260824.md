# C3 proof batch 3 — 2026-08-24

Target: the **unconditional half-plane domination** consumed by
`XiStructure.rh_iff_xiStructure_dominates`, i.e.

```
∀ z : ℂ, 0 < z.im → ‖Estar xiStructure z‖ ≤ ‖xiStructure z‖
```

with no new axiom, no placeholder, and no Prop-valued hypothesis in the final signature.
All Lean under `tmp/`; nothing in `RequestProject/` touched; no commits.
Every COMPILED item below has real `lake env lean` output and `#print axioms` showing
`{propext, Classical.choice, Quot.sound}`; escape-hatch scan (`sorry|admit|axiom|
native_decide|unsafe`) on all four scratch files returns clean.

**Executed attacks: 26.**  Final RH/GRH theorem: **not compiled.**

## OpenAI adjudication after batch completion

The batch-3 disposition of `T(r,x) ≥ 0` as OPEN is superseded by the earlier
arbitrary-precision convergence study in `tmp/att532_x60_convergence.txt`.
The normalizations match as follows.  Batch 3 uses the Riemann kernel `φ`, whereas
`att532` uses `P0 = φ/2`; consequently its Wigner density is `W_x = C/4` and its tail
is `S_x = T/4`.  Therefore the four stable evaluations

```
S_60(0) = -6.1028536779278205914e-37
```

at 40, 50, 60, and 70 decimal digits imply

```
T(0,60) = -2.4411414711711282366e-36 < 0.
```

Hence uniform ramp-tail positivity is **FAILED**, not OPEN.  The compiled implication
`T ≥ 0 -> sinh pairing ≥ 0` remains correct as an abstract theorem, but its proposed
Xi premise is false.  The surviving analytic direction is the compensated integral
seen in `tmp/att536_out.txt`: the negative initial tail followed by a larger positive
lobe against the increasing weight `g_y''`.  A uniform single-crossing or weighted
compensation theorem is the next analytic target.

---

## 0. Corrections carried in from the interrupted runs

* **Normalization.**  `att537` used `Ξ(x) = 2∫_ℝ φ e^{ixu}du`, which is **twice**
  `ξ(1/2+ix)`.  The correct constant is `c = 1`
  (Titchmarsh 2.16.1: `Ξ(x) = 2∫_0^∞ Φ(u)cos(xu)du = ∫_ℝ φ(u)e^{ixu}du`), verified to
  `1e-16` at `x = 0,1,5,14.134725,25,40` (`att538_out.txt`, block `N0`).  Every constant
  below is in the corrected normalization; `att537`'s constants are void.
* **Retraction.**  `att537` displayed `L_1(60) < 0`.  Recomputed at `dps = 40`:
  `L_1(60) = +6.829885024e-35`.  It was double-precision cancellation (≈17 digits lost).
  Withdrawn.
* **`att540` block B6 print bug.**  The row labelled `L_n` is in fact
  `D_{2n} = d^{2n}/dh^{2n}[Ξ(x+h)Ξ(x−h)]|_0`; the true `L_n = (−1)^n D_{2n}`.  The B6
  *conclusion* is unaffected — see the recomputation there.
* **Method.**  All 2401² grids are retired.  Everything now runs through the 1-D
  convolution form, and every hostile sign through a Ξ-only cancellation-free form.

---

## 1. The exact representation the batch produced (EQUIV)

Derived and verified this batch; it is the frame the rest of the register lives in.
With `φ` = even extension of Riemann's `Φ`, define the **cell density** (the Wigner
distribution of `φ`)

```
C(u,x) := ∫_ℝ cos(xd) φ(u+d/2) φ(u−d/2) dd = 2∫_ℝ φ(u+v)φ(u−v)cos(2xv) dv
```

Then, all verified numerically to `1e-16` (`att538_out.txt`, block `N1`):

| identity | status |
|---|---|
| `∫_ℝ C(u,x) du = Ξ(x)²` | 1e-16 |
| `4^n ∫ u^{2n} C du = L_n(x) := (−1)^n d^{2n}/dh^{2n}[Ξ(x+h)Ξ(x−h)]｜₀` | 1e-16, n = 1,2 |
| `L_1 = 2(Ξ′² − ΞΞ″)` — the batch-2 "pointwise L1" | 1e-16 |
| **`|Ξ(x+iy)|² = ∫_ℝ e^{−2yu} C(u,x) du`** (two-sided Laplace transform) | 1e-16 |
| `|Ξ(x+iy)|² = Σ_n L_n(x) y^{2n}/(2n)!` | consequence |
| `∫_ℝ e^{−iλu}C(u,x)du = Ξ(x+λ/2)Ξ(x−λ/2)` | consequence |
| **`T(r,x) := ∫_r^∞ (u−r)C(u,x)du = (1/2π)∫_ℝ cos(λr)·D(λ,x)dλ`**, `D(λ,x) = [Ξ(x)²−Ξ(x+λ/2)Ξ(x−λ/2)]/λ²` | `∫_0^∞T dr = L_1/16` to 1e-6 (dbl) and to 8 digits (mp) |

**Consequences that reorganise the target.**  The target is exactly
`∂_y |Ξ(x+iy)|² ≥ 0` for all real `x`, `y ≥ 0`.  In decreasing strength:

```
(S1) C(u,x) ≥ 0                    ⟹ (S3) ⟹ target      [REFUTED, §3]
(S2) T(r,x) ≥ 0 for r ≥ 0          ⟹ target             [REFUTED at x=60, r=0]
(S3) L_n(x) ≥ 0 for all n ≥ 1      ⟹ target             [open; n = 1 is batch-2's L1]
```

`(S2) ⟹ target` because `m_y(t) = t·sinh(2yt)` has `m_y″ ≥ 0` on `[0,∞)` and the
weighted-tail identity writes `J_{m_y} = 2∫_0^∞ m_y″(r)T(r,x)dr`.  This is the
formalised chain of §2.  **`L_1 ≥ 0` alone is not enough** — the whole hierarchy or the
ramp form is needed; that closes the batch-2 "OPEN" note honestly.

---

## COMPILED

Four scratch files, four clean compiles.

### A1 — low strip `|Re z| < e⁴+2`, and the exact residual — `tmp/c3b3_A1.lean`, **EXIT=0**
First literal line: `import RequestProject.XiStructureSeatBridge`.
Compiler output: `tmp/c3b3_A1.log`, 4 theorems, all `{propext, Classical.choice, Quot.sound}`.
Deprecated `push_neg` (2 occurrences) replaced by `push Not` per instruction.

| # | theorem | content |
|---|---|---|
| 1 | `DVP.conjunct_one` axiom audit (`tmp/c3b3_axaudit.lean`) | `{propext, Classical.choice, Quot.sound}` — **clean, as asked** |
| 2 | `seat_energy_nonneg_of_low` / `xiStructure_dominates_of_low` | unconditional domination for `\|Re z\| < e⁴+2` |
| 3 | `xiStructure_dominates_residual_iff` | half-plane domination **⟺** shallow-high-channel domination |
| 4 | `rh_iff_shallow_channel_dominates` | RH ⟺ domination on `\|Re z\| ≥ e⁴+2`, `0 < Im z < ½ − c/log(\|Re z\|+½)` |

### A3 — the same, sharpened to height 634 — `tmp/c3b3_A3.lean`, **EXIT=0**
First literal line: `import RequestProject.XiStructureSeatBridge`.
`DVP.seat_channel_to_634` (Hardy ladder to `|γ| ≤ 1269/2`, already compiled in
`DVPLadder1269o2`) transports through the `w = −z` chart.  Log: `tmp/c3b3_A3.log`.

| # | theorem | content |
|---|---|---|
| 5 | `xiStructure_dominates_of_low634` | unconditional domination for `\|Re z\| ≤ 634` — **11× wider than A1** |
| 6 | `exp_four_le_55` | `e⁴ ≤ 55` |
| 7 | `xiStructure_dominates_residual_iff_634` | residual is now `\|Re z\| > 634` |
| 8 | `rh_iff_shallow_channel_dominates_634` | RH ⟺ shallow channel above 634 |

### A2 — the weighted-tail instantiation at `g_y(u) = u·sinh(2yu)` — `tmp/c3b3_A2.lean`, **EXIT=0**
First literal line: `import RequestProject.WeightedTailPrimitive`.  Log: `tmp/c3b3_A2.log`.
This is the instantiation the batch was asked for, **including the derivative and the
actual Φ-decay integrability**.

| # | theorem | content |
|---|---|---|
| 9 | `gY_deriv_eq`, `gY_deriv2_eq` | `g_y′(u) = sinh(2yu)+2yu·cosh(2yu)`, `g_y″(u) = 4y·cosh(2yu)+4y²u·sinh(2yu)`, as **functions** (so `deriv (deriv g)` is discharged, not assumed) |
| 10 | `gY_zero`, `gY_deriv_zero`, `gY_contDiff`, `gY_deriv2_nonneg` | `g 0 = 0`, `g′ 0 = 0`, `ContDiff ℝ 2`, `g″ ≥ 0` for `y ≥ 0` |
| 11 | `inner_u_abs` + `triF_prod_integrable` | **Φ-decay integrability, reduced**: the product-integrability side condition of `weighted_tail_primitive_identity` follows from the single scalar bound `∫_{u>0} g u·\|W u\| < ∞`, because `∫_0^u (u−r)g″(r)dr = g u` when `g″ ≥ 0` |
| 12 | `nonneg_of_tail_nonneg` | **the triangle-mixture law**: `T(r) ≥ 0 ∀r>0` and `g″ ≥ 0` ⟹ `∫_{u>0} g·W ≥ 0` |
| 13 | `sinh_pairing_nonneg` | the instantiation at `g_y` — `(S2) ⟹ target`, formalised |

Compiler errors actually hit and fixed, in order (from `tmp/c3b3_A2.log`, first run):
1. `simpa [Function.uncurry, triF]` would not close `Measurable (uncurry (triF W g))`
   — replaced by an explicit `funext` equation + `rw`.
2. `rw [IntegrableOn, integrable_indicator_iff, Measure.restrict_restrict]` — the second
   rewrite re-introduces `IntegrableOn`, so a **second** `rw [IntegrableOn]` is needed
   before `restrict_restrict` matches.
3. `rw [hind]` failed against `fun y => uncurry (triF W g) (u, y)` — fixed with a
   defeq `show Integrable (fun r => triF W g u r) _`.
4. `le_or_lt` is not an identifier in this Mathlib — used `le_total`.

### A4 — Hankel refutations and the J-kernel bridge — `tmp/c3b3_A4.lean`, **EXIT=0**
First literal line: `import RequestProject.WeightedTailPrimitive`.  Log: `tmp/c3b3_A4.log`,
12 theorems, all standard axioms.  (A4 ⊇ A2, plus:)

| # | theorem | content |
|---|---|---|
| 14 | `gY_hankel_minor_neg` | `m(0)·m(t) − m(t/2)² < 0` for `m = g_y` — **exponential convexity fails** |
| 15 | `monomial_hankel_minor_neg` | same for every `t^{2n}`, `n ≥ 1` |
| 16 | `jWeight_nonneg`, `jKernel_sinh_eq_gY` | **`2·jKernel d (2u)·sinh(y·2u) = 4·g_y(u)·W_d(u)`** — `JKernelSignLaw`'s vertical-sign integrand *is* the `g_y` pairing, `W_d(u) = Φ(u+d/2)Φ(u−d/2)` |
| 17 | `jKernel_fiber_nonneg_of_tail_nonneg` | each `d`-fiber of the J-kernel pairing is nonneg under ramp positivity + the two honest side conditions |

Note on 11/13/17: `Continuous W` was in the first draft and the linter flagged it unused;
it was removed, so the reduction runs on `Measurable W` alone.

---

## EQUIV

### 18 — the cell-density / Wigner representation (§1)
Every row of the §1 table.  Tagged EQUIV, not progress: it is a **chart** on the target.
Its value is that it makes the target a positivity question about one explicit 1-D
density and supplies the cancellation-free evaluation route.

### 19 — `T(r,x) = (1/2π)∫cos(λr)·D(λ,x)dλ`
Turns the ramp form into a Fourier cosine transform of an object built from `Ξ` alone.
This is what replaced the 2401² grid: no `φ`, no 2-D quadrature, no cancellation.
Checked against `∫_0^∞T dr = L_1/16` at `x = 0, 5, 14.134725` (mp) and `x = 0,5,14,25`
(double, rel ≤ 1.3e-6).

---

## FAILED — refuted by computation or by a compiled inequality

Every one of these was a *sufficient* structure that would have closed the target.
None is a claim about the problem; each is a property of the instrument.

### 20 — (S1) Wigner positivity `C(u,x) ≥ 0` — **REFUTED, stable**
`att538_out.txt`, block `C1`.  `C` is positive for `x ≤ 9` and goes negative from
`x ≈ 12`:

| x | min C | max\|C\| | ratio |
|---|---|---|---|
| 12 | −1.325761e−04 | 2.042417e−04 | **−0.6491** |
| 14.134725 | −2.090776e−05 | 2.090776e−05 | **−1.0000** |
| 21.022 | −1.132906e−09 | 1.705259e−09 | **−0.6644** |
| 25.011 | −5.860807e−12 | 6.937971e−12 | −0.8447 |

Ratios of order 1 against the local scale — not cancellation.  (Points with
`x ≥ 40` are at the double-precision floor and are **not** used.)

### 21 — Gram / autocorrelation factorization (Schoenberg–Widder) — **REFUTED, compiled**
A Hankel kernel `K(a,b) = m((a+b)/2)` is PSD against every nonnegative `φ` iff `m` is
exponentially convex, `m(t) = ∫e^{2λt}dμ(λ)`, `μ ≥ 0` — only then does it factor as
`∫e^{λa}e^{λb}dμ`.  `gY_hankel_minor_neg` and `monomial_hankel_minor_neg` (A4, #14/#15)
kill it at the first `2×2` minor because `m(0) = 0`.
Instrument statement: **no argument using only `Φ ≥ 0` and `Φ` even can reach the
target.**  Cheapest refutation, not run: exhibit an exponentially convex `m` with
`m(0)=0` — impossible, since `m(0)=∫dμ=0` forces `μ=0`.  Consistent with `att525`
(`Φ = ½(δ₁+δ₋₁)+aδ₀`, `a>1`: positive kernel, `cos z + a`, zeros at `π ± i·arccosh a`).

### 22 — two-point log-concavity `Ξ(x)² ≥ Ξ(x+t)Ξ(x−t)`, i.e. `D ≥ 0` — **REFUTED at dps=40**
`att539_out.txt`, block `C1`.  `D` dips negative at 6 of 11 probe abscissae:

| x | min_λ D | at λ | D(0)=L_1/8 |
|---|---|---|---|
| 14.134725 | −6.1280309e−09 | 16.05 | 4.779781e−07 |
| 21.022 | −4.9849485e−12 | 10.05 | 7.8768353e−11 |
| 25.011 | −7.7994764e−15 | 9.15 | 4.0011832e−13 |
| 30.425 | −2.6684268e−17 | 7.15 | 1.4537408e−16 |
| 40 | −3.2498157e−25 | 27.70 | 1.7430444e−22 |
| 60 | −6.8958856e−36 | 4.25 | 8.5373563e−36 |

### 23 — Pólya's criterion on `D` — **REFUTED at dps=40**
`att539_out.txt`, block `B3`.  Pólya: even + nonneg + convex decreasing on `[0,∞)` ⟹
transform ≥ 0, which would give `T ≥ 0` and hence RH.  Both extra hypotheses fail:

| x | concave samples | first at λ | increasing samples | first at λ |
|---|---|---|---|---|
| 0 | 85 | 0.1 | 0 | — |
| 5 | 82 | 0.1 | 0 | — |
| 14.134725 | 122 | 0.1 | 81 | 16.0 |
| 21.022 | 114 | 0.1 | 97 | 10.1 |
| 30.425 | 116 | 0.1 | 103 | 7.1 |
| 60 | 129 | 0.1 | 117 | 4.2 |

Same failure mode as batch-2's B3, now measured on the correct object.

### 24 — total positivity / Hamburger moment problem — **REFUTED, and provably so**
`att540_out.txt`, block `B6` (read with the `L_n = (−1)^n D_{2n}` correction).
`μ_n := ∫u^{2n}C du = L_n/4^n`.  Minors are positive at `x = 0` (0.247, 6.18e−5,
7.74e−11) and `x = 5`, and the `2×2` minor is negative at `x = 14.134725`
(−9.14e−13) and `x = 21.022` (−2.48e−20).
This is not just numeric: **at any zero of `Ξ`,** `μ_0 = Ξ(x)² = 0` while
`μ_1 = L_1/4 = Ξ′(x)²/2 > 0`, so `μ_0μ_2 − μ_1² = −μ_1² < 0`.  Same mechanism as the
compiled #14/#15.

### 25 — variation diminution — **REFUTED**
`att540_out.txt`, block `B7`.  Sign changes of `u ↦ C(u,x)` on `|u| ≤ 1.6`:
`x = 0,5,9 → 0`; `x = 12 → 2`; `14.134725 → 2`; `17 → 4`; `21.022 → 2`; `25.011 → 10`.
The count is not bounded, so no variation-diminishing argument transfers.

### 26 — theta-series term pairing — **REFUTED**
`att540_out.txt`, block `B8`.  The even extension makes **each** term
`Φ_n(|u|) = (4π²n⁴e^{9|u|/2} − 6πn²e^{5|u|/2})e^{−πn²e^{2|u|}}` nonnegative, so the
decomposition `Φ = Σ_n Φ_n` is a decomposition into positive kernels.  It does not help:
the `n = 1` term **alone** has `min C[Φ₁]/max|C[Φ₁]| = −1.0000` at `x = 12`,
`14.134725` and `21.022`.  The obstruction is present in a single term, not created by
the sum.
*(Script docstring bug: the printed line "Φ₁ < 0 near u=0" is wrong — `Φ₁(|u|) > 0`
throughout.  The measured conclusion is unaffected.)*

### 27 — heat flow / de Bruijn `H_t` — **REFUTED**
`att540_out.txt`, block `B9`.  `φ_t(u) = e^{tu²}φ(u)`.  Derived identity:
`C_t(u,x) = e^{2tu²}·[Wigner of φ with an extra e^{2tv²} factor]` — the extra factor
**grows** in `v`, so smoothing should hurt, and it does.  min-ratio at
`x = 12 / 14.134725 / 21.022`:

| t | 12 | 14.134725 | 21.022 |
|---|---|---|---|
| 0.00 | −0.6491 | −1.0000 | −0.6644 |
| 0.10 | −0.7349 | −1.0000 | −0.7614 |
| 0.25 | −0.8588 | −1.0000 | −0.8818 |
| 0.50 | −1.0000 | −1.0000 | −1.0000 |

Monotone degradation.  de Bruijn flow does not restore Wigner positivity.

---

## OPEN

### 28 — (S3) pointwise `L_1(x) ≥ 0` — **no counterexample; not proved**
`att539_out.txt`, block `B1`, `dps = 40`, `x ∈ [0,200]` step `0.5`:
**zero** negatives; min scale-free ratio `L_1/(2Ξ′²+2|ΞΞ″|) = 0.17366691` at `x = 11`.
Hostile points: `L_1(40)=+1.394e−21`, `L_1(60)=+6.830e−35`, `L_1(90)=+1.045e−53`,
`L_1(150)=+1.414e−94`, `L_1(199.5)=+1.074e−126` — all positive.
Per instruction the coefficient Turán result was **not** imported as this pointwise sign,
and I make no claim either way about whether the pointwise statement is classically
known; I did not read it at source this batch.
Structural note earned this batch: even if proved, `L_1 ≥ 0` is **not** sufficient —
`|Ξ(x+iy)|² = Σ L_n y^{2n}/(2n)!` needs the whole hierarchy (or the ramp form), and
`L_1 ≥ 0` alone buys a zero-free region of DVP width only.

### 29 — **(S2) the ramp form `T(r,x) ≥ 0` — superseded: FAILED**
`att540_out.txt`, block `B2`.  Fixed composite Simpson, two cutoffs × two precisions,
no nested adaptive quadrature:

| x | Λ, N, dps | T(0) | T(0.25) | T(1.0) |
|---|---|---|---|---|
| 14.134725 | 40, 1200, 25 | 9.7133392e−07 | 4.5592697e−07 | 1.045e−13 |
| 14.134725 | 80, 2400, 25 | 9.7133414e−07 | 4.5592685e−07 | 4.672e−19 |
| 14.134725 | 40, 1200, 40 | 9.7133392e−07 | 4.5592697e−07 | 1.045e−13 |
| 14.134725 | 80, 2400, 40 | 9.7133414e−07 | 4.5592685e−07 | 4.672e−19 |
| 30.425 | 40, 1200, 25 | 1.0656957e−16 | 1.2458052e−16 | −2.485e−20 |
| 30.425 | 80, 2400, 25 | 1.0644058e−16 | 1.2475396e−16 | +2.213e−22 |
| 30.425 | 40, 1200, 40 | 1.0656957e−16 | 1.2458052e−16 | −2.485e−20 |
| 30.425 | 80, 2400, 40 | 1.0644058e−16 | 1.2475396e−16 | +2.213e−22 |

Reading: `dps 25 ≡ dps 40` to every printed digit ⟹ **no roundoff**; the residual
variation is the finite cutoff `Λ`.  `T(0)` and `T(0.25)` are stable and **positive**
(7 digits at `x = 14.134725`, 3 at `x = 30.425`).  `T(1.0)` sits below the cutoff
resolution and its sign is **not determined** — the `−2.485e−20` at `Λ = 40` is a cutoff
artifact, not a counterexample.  **No stable negative was found.**

The finite-cutoff checks in this subsection did not include `x=60`.  The adjudication
above supplies the missing hostile point and falsifies uniform `T ≥ 0`.  The compiled
implication #12/#13 remains available for other weights, but does not close the Xi case.

### 30 — the residual seat channel
After A3 the residual is `|Re z| > 634`, `0 < Im z < ½ − c/log(|Re z|+½)`.  Inside the
seat's own window law, seat negativity at such an anchor needs a zero **deeper than the
anchor** inside the unit window; so the channel at depth `d` is exactly a zero-free
region of width `d`, and `d → 0` is RH.  This is why no further ladder rung closes it:
raising the ladder moves the height threshold (56.6 → 634) and never the depth.
Cited: `DVP.seat_energy_ge_window`, `DVP.seat_interior_rung_one'`,
`DVP.seat_channel_to_634` — all compiled, all `{propext, Classical.choice, Quot.sound}`.

---

## Skeleton (rule 11), after this batch

```
RH
└─ ∀z, Im z>0 : ‖E*z‖ ≤ ‖Ez‖                        EQUIV   rh_iff_xiStructure_dominates
   ├─ |Re z| ≤ 634                                   COMPILED xiStructure_dominates_of_low634   (#5)
   ├─ |Re z| > 634, deep                              COMPILED xiStructure_dominates_interior_rung
   └─ |Re z| > 634, shallow                           OPEN     rh_iff_shallow_channel_dominates_634 (#8)
      └─ ∂_y|Ξ(x+iy)|² ≥ 0                            EQUIV    §1
         └─ T(r,x) = ∫_r^∞(u−r)C(u,x)du ≥ 0          FAILED at (r,x)=(0,60)
            ├─ ⟹ target                              COMPILED sinh_pairing_nonneg              (#13)
            ├─ side condition ∫ g_y·|W| < ∞           COMPILED triF_prod_integrable             (#11)
            └─ = (1/2π)∫cos(λr)D(λ,x)dλ               EQUIV    §1 / #19
```
Next leaf: prove the weighted compensation directly, allowing the verified negative
initial tail and exploiting the later positive lobe against the increasing `g_y''`.

---

## Artifacts

| file | what |
|---|---|
| `tmp/c3b3_axaudit.lean` / `.log` | `conjunct_one` axiom audit — clean |
| `tmp/c3b3_A1.lean` / `.log` | low strip `e⁴+2` + exact residual, EXIT=0 (deprecated tactics replaced) |
| `tmp/c3b3_A2.lean` / `.log` | `g_y` derivatives, Φ-decay integrability, triangle-mixture law, EXIT=0 |
| `tmp/c3b3_A3.lean` / `.log` | low strip 634 + sharpened residual, EXIT=0 |
| `tmp/c3b3_A4.lean` / `.log` | A2 + Hankel refutations + J-kernel bridge, EXIT=0 |
| `tmp/att538_c3b3_bench1d.py` / `att538_out.txt` | corrected normalization, 1-D cell density, identity battery |
| `tmp/att539_xi_only.py` / `att539_out.txt` | Ξ-only arbitrary-precision `L_1`, `D`, Pólya (B2 block cut short by design) |
| `tmp/att540_c3b3_structures.py` / `att540_out.txt` | total positivity, variation diminution, theta pairing, heat flow, ramp checkpoints |
| `tmp/att537_c3b3_bench.py` | superseded — wrong normalization; retained only as the record of the retraction |

No `RequestProject/` file was created or modified.  No commits.
