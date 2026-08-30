# C3 proof batch 4 — 2026-08-24

Target unchanged: the unconditional half-plane domination consumed by
`XiStructure.rh_iff_xiStructure_dominates`,

```
∀ z : ℂ, 0 < z.im → ‖Estar xiStructure z‖ ≤ ‖xiStructure z‖
```

All Lean under `tmp/`; no `RequestProject/` file created or modified; no commits
(`HEAD` still `da72c64`).  **Executed attacks: 25.**  Final RH/GRH theorem: **not
compiled.**

**Compile record.**  Five files, all `EXIT=0`, `0` errors, **41** `#print axioms` lines,
every one of them exactly `{propext, Classical.choice, Quot.sound}`.  Escape-hatch scan
(`sorry|admit|axiom |native_decide|unsafe|implemented_by`) over all five: **no hits**.

| file | first literal line | EXIT | axiom prints |
|---|---|---|---|
| `tmp/c3b4_A1.lean` | `import RequestProject.WeightedTailPrimitive` | 0 | 6 |
| `tmp/c3b4_A2.lean` | `import RequestProject.WeightedTailPrimitive` | 0 | 9 |
| `tmp/c3b4_A3.lean` | `import RequestProject.XiStructureFunction` | 0 | 11 |
| `tmp/c3b4_A4.lean` | `import c3b4_A2` | 0 | 8 |
| `tmp/c3b4_A5.lean` | `import c3b4_A2` | 0 | 7 |

`A4`/`A5` import the batch's own `A2` as an olean.  Reproduce with
`lake env lean -o tmp/c3b4_A2.olean tmp/c3b4_A2.lean` then
`LEAN_PATH="$(lake env printenv LEAN_PATH):$PWD/tmp" lake env lean tmp/c3b4_A4.lean`.

⟨1⟩ Own scale is `Ξ(x)²` (`8.4638800011871830418e-36` at `x = 60`), never 1.  DC = the
`r`-independent `Ξ(x)²/τ²` mode, integrated in closed form; AC = the
`Ξ(x+τ)Ξ(x−τ)` mode, the only thing quadratured.  ⟨2⟩ Every cumulative moment below is
evaluated exactly before anything is estimated (`M(∞) = L₁/16`, checked to 1e-17 against
an independent `Ξ`-derivative route).  ⟨3⟩ Retrieved `weighted_tail_primitive_identity`,
`JKernelSignLaw`, `XiStructureFunction` at source rather than reconstructing.

---

## 0. Geometric correction carried in this session (Sam) — and compiled, not asserted

Batch 3 wrote "low **strip** `|Re z| < e⁴+2`" and "`|Re z| ≤ 634`".  That phrasing invites
reading the bound as a strip in the native `s`-plane.  It is not.  `XiStructureFunction`
line 47 defines `E(z) = ξ(½ − iz) + ξ′(½ − iz)`, so the chart is

```
s = ½ − i z            z = i (s − ½)
Re z = −Im s           the ORDINATE (height t)          zOfS_re      COMPILED
Im z = Re s − ½        the DEPTH off the critical line  zOfS_im      COMPILED
```

Consequences, all compiled in `tmp/c3b4_A3.lean`:

* **`|Re z| ≤ 634` is an ORDINATE BAND `|Im s| ≤ 634`** (`band_is_ordinate`).  It places
  no condition at all on `Re s`.  This is exactly why raising the Hardy ladder moves the
  height threshold (56.6 → 634) and never the depth, as batch 3 §30 observed without
  naming the reason.
* **The native helix domain is `Re s > 0`** — where phasors enter the bank at zero
  magnitude and grow — and in the chart that is `Im z > −½` (`native_domain_iff`).  The
  entry wall `Re s = 0` is the chart line `Im z = −½` (`entry_wall_iff`).  The domination
  criterion lives on `Im z > 0`, i.e. `Re s > ½` (`upper_half_iff_right_of_critical`) —
  the RIGHT HALF of the native domain, not all of it.  `Re s > 1` is the abscissa of the
  projected Dirichlet series and never enters (ground rule 4).
* **`E` and `E*` are the conjugate double-helix / anti-helix pair.**  Chart conjugation
  is the functional-equation reflection: `sOfZ (conj (zOfS s)) = 1 − s̄`
  (`conj_chart_is_fe_reflect`), an involution (`fe_reflect_involutive`), whose fixed set
  is `Re s = ½`, the chart's real axis (`critical_line_iff`).  So `‖E* z‖ ≤ ‖E z‖` on
  `Im z > 0` says: **on the side `Re s > ½` the helix dominates its anti-helix**, the
  reading of the same structure function at the mirror point across the critical line.

Everything in this section is a compiled theorem about the map; nothing is asserted.

---

## 1. What batch 3 left, and what moved

Batch 3's leaf was the linear ramp `T(r,x) = ∫_r^∞ (u−r)C(u,x)du ≥ 0`, refuted by the
adjudicated `T(0,60) = −2.4411414711711282366e-36`.  This batch replaces it, in two
strictly weakening steps, and then cuts the survivor to a compact window:

```
(S2)  T(r,x) ≥ 0 for all r ≥ 0                                  FAILED  (x=60, r=0)
(S2ᴬ) T ≤ 0 on (0,r₀], T ≥ 0 on (r₀,∞), ∫₀^∞ T ≥ 0              superseded by (S2ᴮ)
(S2ᴮ) U(s) := ∫_s^∞ T(r,x)dr ≥ 0 for all s ≥ 0                  OPEN, no counterexample
      ≡ ∫_s^∞ (u−s)²/2 · C(u,x) du ≥ 0   (QUADRATIC RAMP)       second_tail_eq_quadratic_ramp
(S2ᶜ) (S2ᴮ) restricted to the COMPACT window 0 ≤ s ≤ u₀(x)      OPEN — what remains
```

`(S2ᴬ) ⟹ (S2ᴮ)` is compiled (`second_tail_nonneg_of_single_crossing`), and the converse
fails, so `(S2ᴮ)` is kept and `(S2ᴬ)` recorded as superseded.  `U(0) = L₁(x)/16`, so the
`s = 0` instance of `(S2ᴮ)` is exactly `L₁ ≥ 0`.

---

## COMPILED

### A1 — weighted single-crossing compensation (DECOMPOSITION A) — `tmp/c3b4_A1.lean`, **EXIT=0**

| # | theorem | content |
|---|---|---|
| 1 | `weighted_single_crossing_nonneg` | `S ≤ 0` on `(0,r₀]`, `S ≥ 0` on `(r₀,∞)`, `∫S ≥ 0`, `q` monotone on `[0,∞)`, `q 0 ≥ 0` ⟹ `∫ q·S ≥ 0`.  Chebyshev pivot at `q r₀`; no continuity, differentiability or growth assumed on `q` |
| 2 | `gY''_monotoneOn` | **`g_y″` is NONDECREASING on `[0,∞)` for `y ≥ 0`** — the property that makes compensation available at all |
| 3 | `triF_measurable`, `inner_u_abs`, `triF_prod_integrable` | Φ-decay integrability reduced to the scalar bound `∫_{u>0} g u·\|W u\| < ∞` (reproduced self-contained; the sinh-bridge file has no olean) |
| 4 | `sinh_pairing_nonneg_of_single_crossing` | composition through `weighted_tail_primitive_identity` |

Errors actually hit and fixed: (i) `simpa using mul_nonneg (neg_nonneg…) …` simplified to
`(q r0 − q r)*S r ≤ 0`, the wrong orientation — replaced by an explicit `h3` plus
`linarith`; (ii) `WeightedTail.triF_prod_integrable` is **not** in
`RequestProject.WeightedTailPrimitive` (it lives in the unbuilt `WeightedTailSinhBridge`),
so it was reproduced locally.

### A2 — the SECOND tail primitive (DECOMPOSITION B) — `tmp/c3b4_A2.lean`, **EXIT=0**

| # | theorem | content |
|---|---|---|
| 5 | `inner_s`, `inner_r_shift`, `tail_shift_identity` | **the layer-cake Fubini**: `∫_{(0,∞)}(p − p 0)·V = ∫_{(0,∞)} p′(s)·(∫_{(s,∞)}V)`.  Written like `WeightedTailPrimitive` so no boundary term at infinity is ever needed |
| 6 | `triG_measurable`, `inner_s_abs`, `triG_prod_integrable` | layer-cake integrability reduced to `∫_{r>0}(p r − p 0)·\|V r\| < ∞` |
| 7 | `gY''_hasDerivAt`, `gY''_deriv_eq`, `gY'''_nonneg`, `gY''_contDiff` | `g_y‴(u) = 12y²sinh(2yu) + 8y³u·cosh(2yu)` as a **function**, so `deriv (gY'' y)` is discharged, not assumed; `≥ 0` on `[0,∞)` |
| 8 | `weighted_second_tail_nonneg` | **the abstract theorem**: `∫_{(s,∞)}V ≥ 0` for every `s ≥ 0`, `p 0 ≥ 0`, `p′ ≥ 0` on `(0,∞)` ⟹ `∫ p·V ≥ 0`.  **NO sign hypothesis on `V` whatsoever** |
| 9 | `sinh_pairing_nonneg_of_second_tail`, `…'` | the deliverable, and the variant with layer-cake integrability discharged |

Error actually hit and fixed, and it is a real mathematical one: my first draft assumed
`hpd : ∀ s, 0 ≤ deriv p s` globally.  **`g_y‴` is ODD**, hence strictly negative on
`(−∞,0)`, so that hypothesis is unprovable at the intended instance.  The compiler goal
`⊢ False` from `this : 0 ≤ gY''' y (−s)`, `a✝ : −gY''' y (−s) < 0` is what caught it.
Fixed by restricting the sign hypothesis of `inner_s_abs` / `triG_prod_integrable` to
`Ioi 0`, which is where the layer-cake integral lives.  Also `ContDiff.differentiable`
wants `n ≠ 0` in this Mathlib, not `1 ≤ n`.

### A3 — the chart map — `tmp/c3b4_A3.lean`, **EXIT=0**
11 theorems; the content is §0 above.  One residual arithmetic goal
(`2⁻¹ + (2⁻¹ − s.re) = 1 − s.re`) closed by appending `<;> ring`.

### A4 — the third tail primitive and the J-kernel — `tmp/c3b4_A4.lean`, **EXIT=0**

| # | theorem | content |
|---|---|---|
| 10 | `triH_inner_u`, `triH_inner_r`, `second_tail_eq_quadratic_ramp` | **`∫_{(s,∞)} T(r)dr = ∫_{(s,∞)} (u−s)²/2 · W(u) du`** — the second tail primitive IS the quadratic ramp, one rung above the refuted linear ramp |
| 11 | `second_tail_nonneg_of_single_crossing` | **the containment**: single crossing + `∫T ≥ 0` ⟹ `U ≥ 0`.  Compiling this is what licenses dropping A in favour of B rather than carrying both |
| 12 | `sinh_pairing_nonneg_of_quadratic_ramp` | the final analytic leaf, in `Ξ`-checkable form |
| 13 | `jWeight_nonneg`, `jKernel_sinh_eq_gY`, `jKernel_fiber_nonneg_of_quadratic_ramp` | the J-kernel `d`-fiber under the WEAKENED hypothesis; `2·jKernel d (2u)·sinh(y·2u) = 4·g_y(u)·W_d(u)` |

### A5 — THE COMPACT REDUCTION — `tmp/c3b4_A5.lean`, **EXIT=0**

| # | theorem | content |
|---|---|---|
| 14 | `tailT_nonneg_of_weight_nonneg`, `tailT_nonneg_above`, `second_tail_nonneg_above` | eventual nonnegativity of the weight propagates to both tail primitives.  **No integrability hypothesis needed** — a non-integrable Bochner integral is `0`, still `≥ 0` |
| 15 | `second_tail_nonneg_of_compact`, `sinh_pairing_nonneg_of_compact` | **`W ≥ 0` on `(u₀,∞)` reduces the half-line hypothesis to the COMPACT window `[0,u₀]`** |
| 16 | `theta_diagonal_perfect_square`, `theta_diagonal_bracket_nonneg` | `16π⁴e^{9u} − 48π³e^{7u} + 36π²e^{5u} = 4π²e^{5u}(2πe^{2u} − 3)²` — the `n=1` theta diagonal's polynomial factor is a SQUARE, so it cannot change sign |

---

## EQUIV

### 17 — the cumulative-moment `Ξ` route, and its exact DC tails
`tmp/att541_c3b4_ramp2.py`.  From att532's validated `S^{Py} = T/4`:

```
T(r,x) = (1/2π) ∫_0^∞ [Ξ(x)² − Ξ(x+τ)Ξ(x−τ)] cos(2rτ) τ^{-2} dτ
M(R,x) := ∫_0^R T dr
       = (1/4π) ∫_0^∞ [Ξ(x)² − Ξ(x+τ)Ξ(x−τ)] sin(2Rτ) τ^{-3} dτ      (absolutely convergent swap)
U(R,x)  = L₁(x)/16 − M(R,x),      L₁ = 2(Ξ′² − ΞΞ″)
```

DC tails in closed form, so only the AC mode is quadratured:
`∫_T^∞ cos(aτ)τ^{-2}dτ = cos(aT)/T − a(π/2 − Si(aT))`, and
`∫_T^∞ sin(aτ)τ^{-3}dτ = sin(aT)/(2T²) + (a/2)·[the above]`.

**Validation (⟨2⟩, DC first).**  `M(R) → L₁/16` at `x = 5`, `dps = 30`, `T = 60`:
`M(2) = M(3) = M(4) = M(6) = 0.0005016796043277887` against `L₁/16 =
0.00050167960432778866703` — relative deviation `6.0e-18 … 1.8e-17`, i.e. two
independent routes (a `Ξ`-derivative evaluation and an oscillatory quadrature) agreeing
to 18 digits.  This is what pins the normalisation for everything below.

### 18 — the `n = 1` theta diagonal is a Macdonald function of imaginary order
`tmp/att543_c3b4_bessel.py`.  With `Φ₁(t) = 2πe^{5t/2}(2πe^{2t} − 3)e^{−πe^{2t}}` and
`a := 2πe^{2u}`, the `n = 1` diagonal of the cell density is EXACT:

```
C₁₁(u,x) = 2[ (16π⁴e^{9u} + 36π²e^{5u})·K_{ix}(a) + 48π³e^{7u}·K′_{ix}(a) ]
```

and as `a → ∞`, `K′/K → −1` and the bracket collapses onto the compiled perfect square:

```
C₁₁(u,x) ~ 8π²e^{5u}(2πe^{2u} − 3)²·K_{ix}(2πe^{2u})
```

**So the sign of the cell density at large `u` is the sign of a Macdonald function of
imaginary order.**  Checked against the independent, cancellation-free `Ξ` route
`C(u,x) = (2/π)∫_0^∞ Ξ(x+τ)Ξ(x−τ)cos(2τu)dτ` at `x = 21.022`, `dps = 30`:

| u | C (Ξ route) | C₁₁ (Bessel) | rel |
|---|---|---|---|
| 0.4 | −4.35859308467e−10 | −3.7243087935e−10 | 0.146 |
| 0.5 | 7.45817837233e−10 | 7.4722455289e−10 | **1.9e−3** |
| 0.6 | 1.56748174573e−9 | 1.56748745744e−9 | **3.6e−6** |
| 0.8 | 1.70452728752e−11 | 1.70452728754e−11 | **1.3e−11** |
| 1.0 | 2.34747438661e−16 | 2.34747438661e−16 | **7.4e−19** |

The identification is confirmed for `u ≳ 0.5` and degrades below it exactly as it should
(the `n ≥ 2` modes and the `|u|` corner are not in `C₁₁`).  `sign C = sign K_{ix}(a)`
held at every probe where the identification holds.

---

## FAILED — refuted by computation, or by a compiled inequality

### 19 — uniform ramp positivity `T ≥ 0` — **FAILED (carried in, adjudicated)**
`T(0,60) = −2.4411414711711282366e-36`, from `S_60(0) = −6.1028536779278205914e-37`
stable at `dps = 40/50/60/70` (`tmp/att532_x60_convergence.txt`).  Reproduced
independently this batch by `att541` at `dps = 40`, `T = 150`:
`T(0,60) = −2.4411414711711e-36`.

### 20 — the `L₁` cache-collision bug — **my own instrument, caught and fixed**
`att541`'s first run printed `L₁(60) = 0.0`, which contradicts att539's
`+6.829885024e-35`.  Cause: the `Ξ` cache was keyed on `mp.nstr(v, 35)`, a decimal
truncation, which collapses the nearby probes `mp.diff` uses into one entry and returns
a numerically exact zero derivative.  Fixed by keying on the exact `(mp.mpf(v), prec)`
pair; `L₁(60) = +6.8298850238089124821e-35` thereafter, matching att539 to 10 digits.
**Recorded because a cache keyed on a rounded string is a silent-zero generator, not a
performance detail.**

### 21 — the apparent SECOND sign change of `T` — **resolution floor, not a crossing**
`att541` hostile sweeps reported `T` sign changes at `r ≈ 1.58` (`x = 60`) and
`r ≈ 1.70` (`x = 88`).  Both are artifacts.  The tell is that the value is **frozen**:

| x | frozen value | over |
|---|---|---|
| 60 | `−1.7731014905…e−65` (11 digits constant) | `r ∈ [1.60, 2.00]` |
| 88 | `−9.6564419714…e−85` (11 digits constant) | `r ∈ [1.72, 2.00]` |

A genuine `T(r) = ∫_r^∞(u−r)C(u,x)du` decays double-exponentially in `r`; a value
independent of `r` to 11 digits across a range where the true object falls by many
orders is an `r`-independent additive error.  The four-precision ladder that would have
quantified the floor (`att542`) was stopped as over-resolved and **was not rerun**, so
the floor magnitude is reported as *observed* (`~1e−65` at `x=60`, `~1e−85` at `x=88`)
and not as a certified bound.  **Consequence for the record: within the RESOLVED range,
`T` has exactly ONE sign change at both hostile abscissae — single crossing is neither
confirmed nor refuted below the floor.**

Same phenomenon, independently, in the `C(u,60)` probe of attack 25: `C` reported at
`~1.3e−38` and flat across `u = 1.7 … 2.0`, where the Bessel form gives `~1e−48`.

### 22 — PREDICTION REFUTED: the `K_{ix}` zero count is **not** `C`'s sign-change count
Pre-registered in `att543`'s docstring before running: I predicted all three checks
(identification / sign law / zero-count mechanism) would confirm, flagging (c) as the one
that could fail.  It failed.

| x | zeros of `K_{ix}(a)` on `(2π,x)` | predicted changes of `C` on `(0,u₀]` | **measured** |
|---|---|---|---|
| 12 | 1 | 1 | — |
| 14.134725 | 2 | 2 | — |
| 17 | 4 | 4 | — |
| 21.022 | 6 | 6 | **1** (at `u = 0.47`, step `0.01`, `dps = 30`) |
| 25.011 | 8 | 8 | — |

Direct `Ξ`-route count at `x = 21.022` on `(0,0.62]`: **one** sign change, not six.  So
the `n ≥ 2` theta modes *suppress* the `n = 1` diagonal's oscillations rather than
inheriting them, and batch 3's measured counts (which I had suspected of being
resolution-limited because they are non-monotone in `x`) are vindicated at this abscissa.
Instrument statement: **the theta-mode decomposition does not transfer oscillation counts
to the full cell density**; a term-by-term argument for the ramp cannot be built this way.

---

## OPEN

### 23 — **(S2ᴮ) `U(s) ≥ 0`** — no counterexample; not proved
`tmp/att541_out_hostile60.txt`, `tmp/att541_out_hostile88.txt`, `dps = 40`, fine
`r`-sweep step `0.02` on `[0,2]`, AC tail bounds measured (not assumed) by a geometric
majorant sampled on `[T, T+1]`.

| x | `Ξ(x)²` | `L₁(x)` | `U(0) = L₁/16` | `T(0)` | min resolved `U` | AC bound |
|---|---|---|---|---|---|---|
| 60 | 8.4638800012e−36 | +6.8298850238089124821e−35 | 4.2686781398805703013e−36 | −2.4411414711711e−36 | **+2.870786607409e−65** at `r=1.56` | 2.4e−102 |
| 88 | 3.7003020724e−54 | +3.6094202044417537148e−53 | 2.2558876277760960718e−54 | −2.8254263063119e−55 | **+3.1162275208596e−84** at `r=1.66` | 5.1e−121 |

(The tabulated `min_R U` at `R = 1.58 / 1.68` in the raw files sits *past* the `T` floor
of attack 21 and is therefore quoted here at the last point before the floor.)
`U ≥ 0` holds at every resolved point at both hostile abscissae, with the margin against
the AC tail bound running 37+ orders of magnitude.  `T(0) < 0` at both — so this is the
compensation actually doing work, not a vacuous restatement of `T ≥ 0`.

### 24 — `L₁(x) ≥ 0` — the `s = 0` instance, carried over from batch 3
att539 block `B1`, `dps = 40`, `x ∈ [0,200]` step `0.5`: zero negatives.  Re-confirmed
this batch at the two hostile abscissae (table above).  Still not proved, and per
standing instruction the coefficient Turán result was **not** imported as this pointwise
sign.

### 25 — `C(u,x) ≥ 0` above `u₀(x) = ½ log(x/2π)` — the input `A5` is built to consume
Supported, not proved.  Evidence: the Bessel identification (attack 18) is confirmed
precisely in this regime, `K_{ix}(a) > 0` for `a > x`, and the polynomial factor is a
compiled perfect square.  Direct checks of the last resolved sign change of `C(·,x)`:

| x | `u₀(x)` | last RESOLVED sign change of `C` |
|---|---|---|
| 21.022 | 0.6038 | `u = 0.47` |
| 60 | 1.1282 | `u = 1.0` (changes reported at `1.3, 1.7` are at the `1e−38` floor; true `C ~ 1e−48` there) |

Two for two, the last crossing falls below `u₀`.  If this is proved, `A5` cuts the open
hypothesis to the compact window `[0, u₀]`, of length `1.13` at `x = 60` and `1.32` at
`x = 88`.

### 26 — the residual seat channel (unchanged from batch 3, restated correctly)
After `xiStructure_dominates_of_low634` the residual is the **ordinate band exterior**
`|Im s| > 634` together with `0 < Re s − ½ < ½ − c/log(|Im s| + ½)`.  Batch 3's "strip"
wording is corrected by §0.  Seat negativity at such an anchor needs a zero deeper than
the anchor inside the unit window, so the channel at depth `d` is exactly a zero-free
region of width `d`, and `d → 0` is RH — which is why no further ladder rung closes it.

---

## Skeleton (rule 11), after this batch

```
RH
└─ ∀z, Im z>0 : ‖E*z‖ ≤ ‖Ez‖                          EQUIV    rh_iff_xiStructure_dominates
   │   [chart: Re z = −Im s, Im z = Re s − ½;         COMPILED c3b4_A3 (11 thms)
   │    E vs E* = helix vs anti-helix, conj = s↦1−s̄]
   ├─ |Im s| ≤ 634  (ORDINATE BAND, not a strip)      COMPILED xiStructure_dominates_of_low634
   ├─ |Im s| > 634, deep                              COMPILED xiStructure_dominates_interior_rung
   └─ |Im s| > 634, shallow                           OPEN     rh_iff_shallow_channel_dominates_634
      └─ ∂_y|Ξ(x+iy)|² ≥ 0                            EQUIV    batch-3 §1
         └─ ∫_{u>0} g_y(u)·C(u,x) du ≥ 0              EQUIV    g_y(u)=u·sinh(2yu)
            ├─ T(r,x) ≥ 0                             FAILED   T(0,60) = −2.4411…e−36
            ├─ single crossing + ∫T ≥ 0               SUPERSEDED  ⟹ next line (attack 11)
            └─ U(s) = ∫_s^∞ T ≥ 0  ∀s ≥ 0             OPEN     ← THE LEAF
               ├─ ⟹ target                            COMPILED sinh_pairing_nonneg_of_second_tail
               ├─ = ∫_s^∞ (u−s)²/2·C du               COMPILED second_tail_eq_quadratic_ramp
               ├─ s=0 instance is L₁ ≥ 0              OPEN     attack 24
               └─ reduces to s ∈ [0, u₀(x)]           COMPILED sinh_pairing_nonneg_of_compact
                  └─ needs C ≥ 0 above u₀             OPEN     attack 25  ← STRONGER-and-constructive
```

**Rule-11 guard check.**  The leaf `U ≥ 0` is `EQUIV`-flavoured (it is a restatement of
the target's positivity at ramp order 2).  The leaf that is **not** a restatement is
attack 25, `C(u,x) ≥ 0` for `u > u₀(x)`: it is an object to be *exhibited* — the sign of
`K_{ix}(2πe^{2u})`, discharged by the identity of attack 18 plus the compiled perfect
square, not by an estimate.  So the skeleton has at least one `STRONGER`-and-constructive
leaf and is a proof plan rather than a restatement.  It is not yet a proof: attacks 23,
24, 25 are all open.

---

## Artifacts

| file | what |
|---|---|
| `tmp/c3b4_A1.lean` / `.log` | single-crossing compensation, `g_y″` monotone, EXIT=0 |
| `tmp/c3b4_A2.lean` / `.log` / `.olean` | layer-cake Fubini, second-tail compensation, `g_y‴`, EXIT=0 |
| `tmp/c3b4_A3.lean` / `.log` | the chart map / geometric correction, EXIT=0 |
| `tmp/c3b4_A4.lean` / `.log` | quadratic-ramp identity, containment, J-kernel fiber, EXIT=0 |
| `tmp/c3b4_A5.lean` / `.log` | compact reduction, theta perfect square, EXIT=0 |
| `tmp/att541_c3b4_ramp2.py` + `att541_out_{prof,hostile}{60,88}.txt` | `M`,`U` route; hostile sweeps.  **`out_prof*` predate the `L₁` cache fix — its `U` column is `−M(R)`; use `out_hostile*`** |
| `tmp/att543_c3b4_bessel.py` + `att543_out_count60.txt` | Macdonald identification, zero counts, direct `C` sign counts |
| `tmp/att542_c3b4_floor.py` | written, **stopped as over-resolved and not rerun**; produced no output |

No `RequestProject/` file created or modified.  No commits.
