# C3 proof batch 11 — attacking the derivative sign of the tilted cell-density family

Date 2026-08-25.  Working dir `/Users/samuellavery/work/helix_frobenius`, branch
`ladder-campaign-2026-08`.  **No commit made.  No tracked file modified.  `tmp/c3b10_A1/A2/A3`
untouched.**

`AGENTS.md` DOES NOT EXIST in this repository (`find . -maxdepth 3 -iname AGENTS.md` → empty;
root listing shows `CLAUDE.md` only).  I obeyed `CLAUDE.md` instead and record the absence
here rather than silently substituting.

**TARGET LEAF.**  For all real `x` and `y ≥ 0`, in Lean, no `sorry`, no new axiom, no
Prop-valued target hypothesis:

```
0 ≤ ∫ u in Set.Ioi 0, (u * Real.sinh (2*y*u)) * C3B6.Theta.cellDensity x u
```

**HEADLINE.**  The target is now an **exact bilinear form in four one-dimensional moments**,
compiled and axiom-clean, with **no differentiation under the integral sign anywhere**.  The
general sign is NOT proved.  Two fibres of it are (`x = 0`, `y = 0`).  Two counterexample
kernels show which property the instrument is actually missing.

---

## COMPILED

Toolchain: Mathlib v4.31.0 as vendored.  Build command for every file below:

```
LEAN_PATH=tmp lake env lean -o tmp/<f>.olean tmp/<f>.lean
```

Every `#print axioms` line below is **verbatim compiler output**, and every file exited 0
with no `error:` lines.

### 0. Independent re-verification of the batch-10 inputs (not modified)

`LEAN_PATH=tmp lake env lean tmp/c3b10_A1.lean` → **EXIT_A1=0**, 11 lines, all
`[propext, Classical.choice, Quot.sound]`.
`tmp/c3b11_verify_A2.txt` → **EXIT_A2=0**, 10 lines, all clean.
`tmp/c3b11_verify_A3.txt` → **EXIT_A3=0**, 10 lines, all clean.

Verbatim tail of `tmp/c3b11_verify_A3.txt`:

```
'C3B10.cellDensity_cosh_Ioi_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'C3B10.xiWeight_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'C3B10.cellDensity_Ioi_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'C3B10.cellDensity_Ioi_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'C3B10.gY_eq_cosh_deriv' depends on axioms: [propext, Classical.choice, Quot.sound]
EXIT_A3=0
```

**Independent check of the mathematics, not just the compiler.**  I re-derived
`C3B10.bilin_integral` by hand (shear `(u,p) ↦ (u+p,p)`; translation; dilation `|2⁻¹|`) and
confirmed numerically that `∫_{u>0} cosh(2λu)C(x,u)du = ¼(A²+B²)` to relative error
`3.1e-12` (`tmp/c3b11_num_out.txt`, section N1/N2).  The batch-10 four-square statement is
correct but **not reduced**: the parity of `Φ` collapses it to two squares (§A3 below), which
batch 10 did not use.

### 1. `tmp/c3b11_A1.lean` — the two-weight carrier pairing (the engine)

The novelty that unlocks the batch: `c3b10_A1` pairs a weight with **itself**, which is why
its value is a sum of squares and why it cannot see the `λ`-derivative (the tilt
`e^{λ(u+p)}e^{λ(u−p)} = e^{2λu}` factorises, its derivative does not).  Generalising the same
shear to two independent legs:

```lean
theorem carrier_pairing2 (hIP : Integrable P) (hmP : Measurable P)
    (hIQ : Integrable Q) (hmQ : Measurable Q) (x : ℝ) :
    (∫ u : ℝ, ∫ p : ℝ, P (u + p) * Q (u - p) * Real.cos (2 * x * p))
      = 2⁻¹ * (cosMom P x * cosMom Q x + sinMom P x * sinMom Q x)
```

Hypotheses: `Integrable P`, `Measurable P`, `Integrable Q`, `Measurable Q`.  Nothing else.
Verbatim axiom footprint (13/13 declarations):

```
'C3B11.bilin2_measurable' depends on axioms: [propext, Classical.choice, Quot.sound]
'C3B11.bilin2_slice_integrable' depends on axioms: [propext, Classical.choice, Quot.sound]
'C3B11.bilin2_slice_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'C3B11.bilin2_prod_integrable' depends on axioms: [propext, Classical.choice, Quot.sound]
'C3B11.carrierBilin2_eq_bilin2_shear' depends on axioms: [propext, Classical.choice, Quot.sound]
'C3B11.carrierBilin2_prod_integrable' depends on axioms: [propext, Classical.choice, Quot.sound]
'C3B11.bilin2_slice_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
'C3B11.bilin2_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
'C3B11.carrier_pairing2' depends on axioms: [propext, Classical.choice, Quot.sound]
'C3B11.carrier_pairing2_integrable' depends on axioms: [propext, Classical.choice, Quot.sound]
'C3B11.integral_comp_neg_self' depends on axioms: [propext, Classical.choice, Quot.sound]
'C3B11.cosMom_of_odd' depends on axioms: [propext, Classical.choice, Quot.sound]
'C3B11.sinMom_of_even' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### 2. `tmp/c3b11_A2.lean` — THE TARGET, EVALUATED EXACTLY

Four carrier weights (`Φ = riemannXiKernel`):

```lean
def wQ (y t : ℝ) : ℝ := Real.cosh (y * t) * riemannXiKernel t          -- even
def wS (y t : ℝ) : ℝ := Real.sinh (y * t) * riemannXiKernel t          -- odd
def wP (y t : ℝ) : ℝ := t * Real.sinh (y * t) * riemannXiKernel t      -- even
def wR (y t : ℝ) : ℝ := t * Real.cosh (y * t) * riemannXiKernel t      -- odd
```

The mechanism, compiled as `cell_weight_split`: the cell-centre weight does **not** factorise
across the two legs, but `2u = (u+p)+(u−p)` and `sinh` adds, so it is a sum of exactly four
factorised terms:

```lean
theorem cell_weight_split (y u p : ℝ) :
    wP y (u + p) * wQ y (u - p) + wR y (u + p) * wS y (u - p)
      + wS y (u + p) * wR y (u - p) + wQ y (u + p) * wP y (u - p)
      = 2 * (gY y u * (riemannXiKernel (u + p) * riemannXiKernel (u - p)))
```

Four applications of `carrier_pairing2`, then parity kills four of the eight moments
(`sinMom_wQ`, `sinMom_wP`, `cosMom_wS`, `cosMom_wR`), giving

```lean
theorem target_eq (x y : ℝ) :
    (∫ u in Ioi (0 : ℝ), gY y u * cellDensity x u)
      = 4⁻¹ * (cosMom (wQ y) x * cosMom (wP y) x + sinMom (wS y) x * sinMom (wR y) x)
```

**Exact hypotheses: none.**  `x y : ℝ` arbitrary; no `y ≥ 0`, no window, no threshold on `x`,
no Prop-valued hypothesis, no differentiation under the integral.  With
`A = cosMom (wQ y) x`, `A' = cosMom (wP y) x`, `B = sinMom (wS y) x`, `B' = sinMom (wR y) x`
this reads `target = ¼(A·A' + B·B')`.

```lean
theorem target_nonneg_iff (x y : ℝ) :
    0 ≤ (∫ u in Ioi (0 : ℝ), gY y u * cellDensity x u)
      ↔ 0 ≤ cosMom (wQ y) x * cosMom (wP y) x + sinMom (wS y) x * sinMom (wR y) x
```

Supporting analytic input compiled here: `t_xiWeight_integrable` — the linear moment
`t·e^{λt}Φ(t)` is integrable, because `|t| ≤ e^t + e^{−t}` (`abs_le_exp_add_exp`) charges the
linear factor to **one unit of tilt**, and the tilt family is unbounded (batch-10's Gaussian
majorant `xiKernel_abs_gauss`).  No new estimate on `Φ` was needed.

Verbatim axiom footprint (16/16):

```
'C3B11.abs_le_exp_add_exp' depends on axioms: [propext, Classical.choice, Quot.sound]
'C3B11.t_xiWeight_integrable' depends on axioms: [propext, Classical.choice, Quot.sound]
'C3B11.wQ_integrable' depends on axioms: [propext, Classical.choice, Quot.sound]
'C3B11.wS_integrable' depends on axioms: [propext, Classical.choice, Quot.sound]
'C3B11.wP_integrable' depends on axioms: [propext, Classical.choice, Quot.sound]
'C3B11.wR_integrable' depends on axioms: [propext, Classical.choice, Quot.sound]
'C3B11.sinMom_wQ' depends on axioms: [propext, Classical.choice, Quot.sound]
'C3B11.sinMom_wP' depends on axioms: [propext, Classical.choice, Quot.sound]
'C3B11.cosMom_wS' depends on axioms: [propext, Classical.choice, Quot.sound]
'C3B11.cosMom_wR' depends on axioms: [propext, Classical.choice, Quot.sound]
'C3B11.cell_weight_split' depends on axioms: [propext, Classical.choice, Quot.sound]
'C3B11.gY_cellDensity_ae' depends on axioms: [propext, Classical.choice, Quot.sound]
'C3B11.gY_cellDensity_integrable' depends on axioms: [propext, Classical.choice, Quot.sound]
'C3B11.gY_cellDensity_full' depends on axioms: [propext, Classical.choice, Quot.sound]
'C3B11.target_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'C3B11.target_nonneg_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### 3. `tmp/c3b11_A3.lean` — attack outcomes, compiled

```lean
theorem cellDensity_cosh_Ioi_sq (x lam : ℝ) :                 -- FOUR squares → TWO
    (∫ u in Ioi (0 : ℝ), Real.cosh (2 * lam * u) * cellDensity x u)
      = 4⁻¹ * (cosMom (wQ lam) x ^ 2 + sinMom (wS lam) x ^ 2)

theorem target_zero_nonneg {y : ℝ} (hy : 0 ≤ y) :             -- the x = 0 fibre, UNCONDITIONAL
    0 ≤ ∫ u in Ioi (0 : ℝ), gY y u * cellDensity 0 u

theorem target_y_zero (x : ℝ) :                               -- the y = 0 fibre, EXACTLY zero
    (∫ u in Ioi (0 : ℝ), gY 0 u * cellDensity x u) = 0

theorem leaf_nonneg_of_products (x y : ℝ)                     -- smallest sufficient condition
    (hc : 0 ≤ cosMom (wQ y) x * cosMom (wP y) x)
    (hs : 0 ≤ sinMom (wS y) x * sinMom (wR y) x) :
    0 ≤ ∫ u in Ioi (0 : ℝ), gY y u * cellDensity x u

theorem leaf_cauchy_schwarz (A A' B B' : ℝ) :                 -- magnitude only; SIGN-BLIND
    (A * A' + B * B') ^ 2 ≤ (A ^ 2 + B ^ 2) * (A' ^ 2 + B' ^ 2)
```

Note the exact hypotheses: `target_zero_nonneg` needs only `0 ≤ y`; `target_y_zero` and
`cellDensity_cosh_Ioi_sq` need nothing.  Verbatim axiom footprint (10/10):

```
'C3B11.xiWeight_split' depends on axioms: [propext, Classical.choice, Quot.sound]
'C3B11.cosMom_xiWeight' depends on axioms: [propext, Classical.choice, Quot.sound]
'C3B11.sinMom_xiWeight' depends on axioms: [propext, Classical.choice, Quot.sound]
'C3B11.cellDensity_cosh_Ioi_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'C3B11.leaf_cauchy_schwarz' depends on axioms: [propext, Classical.choice, Quot.sound]
'C3B11.leaf_abs_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'C3B11.leaf_nonneg_of_products' depends on axioms: [propext, Classical.choice, Quot.sound]
'C3B11.t_sinh_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'C3B11.target_zero_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'C3B11.target_y_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### 4. Final verbatim exit-code pass (fresh run, all three blocks)

```
LEAN_PATH=tmp lake env lean tmp/c3b11_A1.lean   ...  EXIT_c3b11_A1=0
LEAN_PATH=tmp lake env lean tmp/c3b11_A2.lean   ...  EXIT_c3b11_A2=0
LEAN_PATH=tmp lake env lean tmp/c3b11_A3.lean   ...  EXIT_c3b11_A3=0

grep -c "error" tmp/c3b11_final_A1.txt tmp/c3b11_final_A2.txt tmp/c3b11_final_A3.txt
tmp/c3b11_final_A1.txt:0
tmp/c3b11_final_A2.txt:0
tmp/c3b11_final_A3.txt:0
```

Last line of each log, verbatim:

```
'C3B11.sinMom_of_even'    depends on axioms: [propext, Classical.choice, Quot.sound]
'C3B11.target_nonneg_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'C3B11.target_y_zero'     depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Deliverable scan

```
grep -n "sorry\|admit\|^axiom\|axiom \|implemented_by\|native_decide\|@\[implemented" \
     tmp/c3b11_A1.lean tmp/c3b11_A2.lean tmp/c3b11_A3.lean tmp/c3b11_probe1.lean
EXIT=1   (1 = no matches = clean)
```

39 compiled declarations, 39 with footprint exactly `[propext, Classical.choice, Quot.sound]`.

---

## OPEN

### Smallest remaining leaf

**`target_eq` has removed the integral.**  What is left is a four-scalar sign condition.
Literal next Lean statement (namespaces as they resolve in `tmp/c3b11_A3.lean`):

```lean
theorem leaf_sign (x : ℝ) {y : ℝ} (hy : 0 ≤ y) :
    0 ≤ C3B10.cosMom (C3B11.wQ y) x * C3B10.cosMom (C3B11.wP y) x
      + C3B10.sinMom (C3B11.wS y) x * C3B10.sinMom (C3B11.wR y) x
```

Given this, `C3B11.target_nonneg_iff` closes the TARGET LEAF verbatim, with no further work.

### Strictly smaller sub-leaf: the `y → 0⁺` edge

Expanding the four moments to first order in `y` (`sinh(yt) = yt + O(y³)`,
`cosh(yt) = 1 + O(y²)`) gives `A·A' + B·B' = y·L₁(x) + O(y³)` with

  `L₁(x) = Ξ'(x)² − Ξ(x)·Ξ''(x)`,   `Ξ(x) = ∫ Φ(t)cos(xt)dt`

— the **first Laguerre expression** for `Ξ`.  Confirmed to 10 significant digits at eight
ordinates (`tmp/c3b11_num2_out.txt`, section M3: `Q/y` vs `L₁(x)` agree at
`x = 0, 3, 7, 14.134725142, 14.5, 21.022039639, 25.010857580, 40`).  Literal next Lean
statement for the edge, written purely in moments of the compiled kernel:

```lean
theorem laguerre_edge (x : ℝ) :
    0 ≤ (∫ t : ℝ, t * riemannXiKernel t * Real.sin (x * t)) ^ 2
      + (∫ t : ℝ, riemannXiKernel t * Real.cos (x * t))
        * (∫ t : ℝ, t ^ 2 * riemannXiKernel t * Real.cos (x * t))
```

**Literature status: NOT CHECKED.**  This session had no web access, and rule 10's novelty
trigger forbids me asserting that this is or is not already known.  It is the first Laguerre
inequality for `Ξ` and there is a Csordas–Norfolk–Varga-adjacent literature on Turán/Laguerre
inequalities for `Ξ`; **read it at source before claiming anything either way.**  Flagged as
the single highest-value literature check coming out of this batch.

### Also open, and cheap

* `HasDerivAt (fun lam => cosMom (wQ lam) x) (cosMom (wP y) x) y` and its `sinMom` partner —
  i.e. that `A'`, `B'` really are the `λ`-derivatives of `A`, `B`.  True by dominated
  convergence with batch-10's Gaussian majorant; **not compiled**.  Only the EQUIV discussion
  below needs it; `target_eq` does not.

---

## EQUIV (navigation only — never a stop reason)

Stating the equivalence because it tells us *where the leaf already lives in this repo*, and
because rule 0 and rule 10 make strength a fact about content, never a verdict on effort.

**The leaf is `Re[ξ′/ξ] ≥ 0` on `Re s ≥ ½`.**  Chain (pencil, each link checked):

1. `A + iB = M(y+ix)` with `M(z) = ∫ e^{zt}Φ(t)dt` (immediate from `cosMom`/`sinMom` and
   `Φ` even), and `A' + iB' = M'(z)`.  Hence `A·A' + B·B' = Re[M'(z)·conj M(z)]`.
2. `M(z) = 2·ξ(½ + z)`.  **Measured, not assumed**: `tmp/c3b11_num_out.txt` §N2b gives
   `A+iB` vs `4·ξ(½+y+ix)` at five `(x,y)` with ratio exactly `2` to 8 digits; §M1 of
   `tmp/c3b11_num2_out.txt` then reproduces the quadrature `Q` and `|M|²` from
   `4|ξ|²·Re[ξ′/ξ]` to full double precision for `x ≤ 30`.  A compiled bridge exists in
   principle via `CriticalLinePhasor.XiKernelBridge.riemannXiKernel_eq_op`
   (`Φ = ψ″ − ψ/4`, `RequestProject/XiKernelThetaBridge.lean:226`) but was NOT wired here.
3. So leaf `⟺ Re[ξ′/ξ](½+y+ix) ≥ 0` for `y ≥ 0` `⟺ |ξ(σ+it)|` nondecreasing in `σ ≥ ½`.
4. `RH ⟹ leaf`: `Re[ξ′/ξ](s) = Σ_ρ (σ−β)/((σ−β)²+(t−γ)²) ≥ 0` when every `β = ½ ≤ σ`.
   `leaf ⟹ RH`: a zero `β+iγ` with `β > ½` makes `F(λ) = ¼|M(λ+iγ)|²` vanish at
   `λ = β−½ > 0` while `F ≥ 0` and (by the leaf) nondecreasing on `[0, β−½]`, forcing
   `F ≡ 0` there, hence `M ≡ 0` by the identity theorem — contradiction.  This direction
   uses the uncompiled differentiation step above.

**Repo home.** `RequestProject/DVPSeatRealPart.lean:62`,
`xi_logDeriv_one_sub_conj : ξ′/ξ(1 − s̄) = −conj(ξ′/ξ(s))`, is exactly the functional-equation
reflection that exchanges the leaf with the compiled seat sign condition
(`Re[ξ′/ξ] ≤ 0` for `Re s < ½`, memory `seat-sign-condition-form`).  **What batch 11 adds is a
new route into that condition that touches no resolvent and no contour**: a real,
one-dimensional, four-moment identity on the carrier.  That is navigation, and the work
continues in OPEN above.

---

## FAILED

Concrete counterexamples and concrete compiler/derivation failures.  Nothing here is a
theorized obstruction; each was ENCOUNTERED.

### F1. Positivity of the kernel is NOT the missing property — explicit counterexample

`Φ_c(t) = e^{−t²}(2 + cos 2t)` is strictly positive, even, Schwartz.  Its two-sided Laplace
transform has the closed form `M_c(z) = √π e^{z²/4}(2 + e^{−1}cos z)`, with zeros exactly
where `cos z = −2e`, i.e. `z₀ = π ± i·arccosh(2e)`.  Verbatim
(`tmp/c3b11_num2_out.txt` §M4a):

```
zero at z0 = (3.14159265358979 + 2.37772652459815j);  M_c(z0) = (-1.7793383e-30 + 8.4471746e-31j)
|M_c(i*Im z0)|  = 1.725062786   (>0, on the imaginary axis)
|M_c(z0)|       = 1.969668114e-30   (=0, OFF the imaginary axis)
  x0=2.3777265246  y=2.40   Q_c = -6.21307409e-01
  x0=2.3777265246  y=2.60   Q_c = -3.06248749e+00
  x0=2.3777265246  y=2.80   Q_c = -6.29358203e+00
  x0=2.3777265246  y=3.00   Q_c = -7.19124073e+00
  x0=2.3777265246  y=3.10   Q_c = -3.41464607e+00
```

**Consequence, stated as a property of the instrument:** the two-weight pairing identity
`target_eq` holds verbatim for every integrable even kernel, so *any* argument that derives
the sign from `Φ > 0` + evenness + the shear alone is refuted by `Φ_c`.  The property
actually required is **"the cosine transform of `Φ` has only real zeros"**, which for `Φ_Ξ`
is the content of the leaf itself.

### F2. Complete monotonicity / Bernstein representation does not deliver the sign

> **CORRECTED IN BATCH 12 (2026-08-25).**  Batch 11 asserted here that *every* Gaussian
> mixture except a single Gaussian fails the target.  **That claim is withdrawn: it was not
> proved.**  The sketch ran "mixture ⟹ cosine transform > 0 ⟹ no zeros on `iℝ` ⟹ (Hadamard,
> order ≤ 2) `M = e^{az²+b}` ⟹ single Gaussian".  Two gaps, both real: (i) a general mixture
> `∫e^{−st²}dμ(s)` need not have an entire two-sided Laplace transform at all, let alone one
> of finite order — that needs hypotheses on `μ` near `s = 0` and near `s = ∞` which were
> never stated; (ii) even granted entirety, "order ≤ 2 and zero-free ⟹ `e^{quadratic}`" is
> Hadamard and requires the order bound, which was assumed, not derived.  **What survives is
> exactly the explicit two-Gaussian example below**, and it survives by closed-form
> computation, not by the class argument.

**The counterexample that stands: `Φ_g(t) = e^{−t²} + e^{−4t²}`.**  This is positive, even,
Schwartz, and `Φ_g(√·)` is completely monotone (a two-atom Bernstein measure).  Its two-sided
Laplace transform is the closed form `M_g(z) = √π e^{z²/4} + (√π/2)e^{z²/16}`, whose zeros
solve `e^{3z²/16} = −½`, i.e. `z² = (16/3)(−log 2 + iπ(2k+1))`.  Verbatim
(`tmp/c3b11_num2_out.txt` §M4b):

```
zero z = (2.59435455359 + 3.22915786432j)   M_g(z) = (-9.86076e-32 + 9.86076e-32j)   Re z = 2.594355 != 0
so with x = Im z = 3.229158: |M_g(i x)|^2 = 3.511789e-01 > 0
                       but |M_g(2.5944 + i x)|^2 = 1.944692e-62 = 0
  x=3.229158  y=1.2972   Q_g = -5.53140584e-02
  x=3.229158  y=1.8160   Q_g = -1.24854532e-01
  x=3.229158  y=2.2052   Q_g = -1.68281720e-01
  x=3.229158  y=2.4646   Q_g = -1.09947960e-01
```

**What this does and does not establish.**  It establishes, by closed form, that *complete
monotonicity of `Φ(√·)` is not sufficient*: here is a completely monotone example that fails.
It does **not** establish anything about the class of all such kernels.  A correct class
statement would need hypotheses of the form "`μ` supported in `[s₀, s₁]` with `0 < s₀ ≤ s₁ < ∞`
and at least two atoms", under which `M` is a finite/uniformly-convergent sum of Gaussians of
order 2 and the Hadamard step is legitimate; **that theorem is not proved here and is not
claimed.**  (Two earlier passes on this control were wrong in opposite directions:
`tmp/c3b11_num.py` §N5 asserted `M_g` was zero-free — false; the batch-11 ledger then asserted
the whole-class statement — unproved.  Only the displayed example is load-bearing.)

### F3. Total positivity / Pólya-frequency route — wrong class

A Pólya-frequency function's bilateral Laplace transform is `1/(e^{γz²+δz}∏(1+δ_k z)e^{−δ_k z})`,
i.e. **zero-free**.  `Ξ` has zeros.  So `Φ_Ξ` is not PF and total positivity is the wrong
cone.  Derived, not asserted.

### F4. Cauchy–Schwarz completion — sign-blind by construction

Compiled as `leaf_cauchy_schwarz` / `leaf_abs_le`.  The bound is invariant under
`(A',B') ↦ (−A',−B')`, so no norm inequality in this family can produce the sign.  This is a
property of the certificate class, exhibited in the compiled statement.

### F5. Helix / anti-helix conjugate cancellation — the branches are EQUAL, not opposite

Symmetrising the `(t,s)`-form of the leaf produces two branches,
`u·sinh(2yu)cos(2xp)` and `p·sinh(2yp)cos(2xu)` — carrier weight and chart clock exchanged,
the conjugate (anti-helix) branch.  But the fibre reflection `s ↦ −s` maps one branch to the
other and leaves `Φ(t)Φ(s)dt ds` invariant (`Φ` even), so the two branches are **equal**.
There is no conjugate cancellation to harvest; the anti-helix reproduces the same quantity.

### F6. Chebyshev / FKG covariance rearrangement — hypothesis not inhabitable

The carrier measure `Φ(u+p)Φ(u−p) du dp` is not a product measure, so the leaf is a genuine
covariance between `g(u)=u sinh(2yu)` (increasing) and `h(p)=cos(2xp)`.  Chebyshev/FKG needs
both factors monotone in the same order; `cos(2xp)` is not monotone in `p` for any `x ≠ 0`.
The hypothesis is uninhabitable at the intended object (cf. `interface-inhabitability-law`).

### F7. Theta-ODE differential inequality — no reduction

`riemannXiKernel u = ψ″(u) − ψ(u)/4` (`XiKernelThetaBridge.lean:226`).  Substituting into the
two-leg product gives `(ψ″−ψ/4)(u+p)·(ψ″−ψ/4)(u−p)`; the second-order operator does not
factor across the legs, so no `y`-differential inequality is produced.  Attempted, abandoned.

### F8. Theta-mode diagonal/off-diagonal domination — refuted by batch 9

`cellDensity_eq_tsum` gives `C = 16 Σ_{n,m} modeTerm`, diagonal modes carrying `cos(0) = 1 > 0`.
Domination fails: on the window the negative lobe is within a factor ≈ 6 of the positive one at
`x = 14.134725` (batch-9 numerics, cited in `tmp/c3b10_A1.lean:7–9`).  Not re-run.

### F9. Bessel/Macdonald representation — reproduces F8

The modes are already exactly evaluated as `C3B5.A2.radial` (K-Bessel) inside `modeTerm`; the
radial factor is positive but multiplied by `cos(x·modeLam n m)`, so the Bessel form is F8 in
another vocabulary and fails identically.

### F10. Compact-window second-tail repair — backwards

Batch 9's `sinh_pairing_from_compact_window` consumes `cellDensity ≥ 0` **pointwise** on a
window.  `target_eq` shows the leaf is an *integrated* statement, strictly weaker than the
pointwise one.  So the window route asks for more than the leaf needs; the repair direction is
backwards, and the correct move is `target_eq`, which bypasses the window entirely.

### F11. Compiler failures encountered (all repaired)

* `MeasureTheory.integral_comp_neg_eq_self` — **does not exist** in this Mathlib.  Replaced by
  `Measure.integral_comp_mul_left f (-1)` (probe `tmp/c3b11_probe1.lean`, compiles silently).
* `mul_nonneg_of_nonpos_nonpos` — does not exist; replaced by `nlinarith`.
* `rw [← integral_add …]` on a four-fold sum: `rw` could not match the lambda-application form
  after the first rewrite.  Repaired by giving each `integral_add` an explicit type ascription
  in a `have` and combining with `rw`/`linarith`.  **Reusable law: never `rw` a Mathlib
  `integral_add` backwards into a merged integrand; ascribe the type and let elaboration do
  the higher-order unification.**
* `linear_combination (2·u·Φ(u+p)·Φ(u−p)) * hadd` had the wrong sign; residual printed as
  `4u(…) = 0`, fixed by negating the coefficient.

---

## NUMERICAL (nonrigorous controls)

Scripts: `tmp/c3b11_num.py` → `tmp/c3b11_num_out.txt`; `tmp/c3b11_num2.py` →
`tmp/c3b11_num2_out.txt`.  Both exit 0.

**N1/N2 — the compiled identity, checked against a direct 2D quadrature.**  `T_mom` is
`¼(AA′+BB′)`; `T_dir` is the `(u,p)` double integral of `u sinh(2yu)Φ(u+p)Φ(u−p)cos(2xp)`:

```
x=  0.000000 y= 0.700  T_mom= 8.1704441615e-03  T_dir= 8.1704441615e-03  relerr=1.12e-12
x=  3.000000 y= 1.000  T_mom= 8.2285166944e-03  T_dir= 8.2285166944e-03  relerr=5.84e-13
x= 14.134725 y= 0.400  T_mom= 7.8144735460e-07  T_dir= 7.8144735519e-07  relerr=7.56e-10
                       F_mom= 3.0923452975e-07  F_dir= 3.0923452997e-07  relerr=6.89e-10
```

**N2b — the `Ξ` identification.**  `A+iB` vs `4·ξ(½+y+ix)`; ratio exactly `2`:

```
x=    5.000000 y= 0.80  A+iB =  5.50103162e-01 +1.07405455e-01i   4xi =  1.10020632e+00 +2.14810910e-01i
x=   21.022000 y= 0.25  A+iB =  1.67039610e-06 -8.75580503e-06i   4xi =  3.34078849e-06 -1.75116100e-05i
```

**M1 — RETRACTION of the part-1 "negatives".**  The first hostile scan reported 15125
negative `Q` values from `x ≈ 30` upward.  **Those are quadrature artefacts, not data.**  At
`x = 46.1, y = 0.5` the double-precision quadrature returns `|M|² = 9.14e-24` where the true
value is `1.64e-24` — the absolute error of a quadrature whose integrand has scale 1 is
`~1e-12`, so `|M| ~ 1e-12` is the noise floor and everything beyond `x ≈ 35` was noise:

```
x=   30.000000 y=0.5   quad Q= 2.919223e-15  |M|^2= 2.282407e-15
                      mpmath Q= 2.919099e-15  |M|^2= 2.282457e-15   -> quadrature |M|^2 error 4.97e-20
x=   46.100000 y=0.5   quad Q=-2.975113e-26  |M|^2= 9.141000e-24
                      mpmath Q= 4.879876e-25  |M|^2= 1.638546e-24   -> quadrature |M|^2 error 7.50e-24
```

**M2 — the hostile scan, redone at 30 dps through `Q = 4|ξ|²·Re[ξ′/ξ]` with `ξ′/ξ` from the
closed form (one `zeta`, one `zeta'`, one `digamma`, no cancellation).**  Grid: `x = 0(0.5)150`
plus all 53 zero ordinates through 150.05 at offsets `±{0.001, 0.01, 0.05}` and `0`;
`y ∈ {1e-6, 1e-4, 1e-2, 0.1, 0.25, 0.49, 0.5, 0.51, 1, 2, 3.5, 5}`:

```
  scanned 8064 (x,y) pairs;  negatives found: 0
  min of Q/|M|^2 = 4.62099862e-08  at x=0.000000, y=1e-06
```

> **CORRECTED IN BATCH 12 (2026-08-25), two items.**
>
> **(i) Normalisation.**  `Q = Re[M′·conj M] = ½ d/dy |M|²`, hence
> `Q/|M|² = ½ d/dy log|M|² = d/dy log|M| = Re[ξ′/ξ](½+y+ix)`.  Batch 11's script and ledger
> printed `Q/|M|² = 2·d/dy log|M|`; **that factor 2 is wrong**.  Nothing downstream changes:
> the scan used only `sign(Q)`, and `Q = |M|²·Re[ξ′/ξ]` is computed exactly, so the reported
> counts and the minimum ratio are unaffected — only the label on the ratio was wrong.
>
> **(ii) The `x = 0` row.**  `Qmp` substitutes `x = 1e-6` whenever `x == 0`, so the row printed
> as `x=0.000000` is a **numerical limit, not an evaluation at `x = 0`**.  Reason: the closed
> form `ξ′/ξ(s) = 1/s + 1/(s−1) − ½logπ + ½ψ(s/2) + ζ′/ζ(s)` has a **removable** singularity at
> `s = 1` — the pole of `1/(s−1)` cancels the pole of `ζ′/ζ(s) = −1/(s−1) + O(1)` — but each
> summand is separately singular, and `(x,y) = (0, ½)` is exactly `s = 1`.  `mpmath` raises
> `ValueError: zeta(1) pole` there, which is how the substitution was introduced.  At
> `x = 1e-6` the displaced value differs from the limit by `O(10⁻¹²)` relative, far above the
> reported minimum `4.62e-08`, so the row is meaningful — but it is a limit and is now labelled
> as one.

**NULL — no falsification.**  Per the falsifiability register this is a non-hit, and it is
reported as such: it is consistency, not evidence of a proof.

**M3 — the `y→0⁺` edge.**  `Q/y` at `y = 1e-8` against `L₁(x) = Ξ′² − ΞΞ″`, 10 digits:

```
  x=    0.000000   Q/y =  4.5679323338e-02   L1(x) =  4.5679323338e-02
  x=   14.134725   Q/y =  7.6476483164e-06   L1(x) =  7.6476483164e-06
  x=   25.010858   Q/y =  6.4029615208e-12   L1(x) =  6.4029615208e-12
  L1 scanned on x in [0,150] step 0.25: negatives = 0;  min L1 = 2.827883e-94 at x=150.0000
```

**M4 — the two counterexample kernels.**  Reproduced verbatim in FAILED F1/F2.

**No mathematical route is declared successful on numerical grounds.**  The only mathematical
claims made in this batch are the compiled ones.

---

## SEARCH COMMANDS

```
find . -maxdepth 3 -iname "AGENTS.md" -not -path "*/.lake/*"          # → empty
rg -n "cellDensity" --glob '!.lake' -l
rg -n "cellDensity" tmp/c3b6_A10.lean
rg -n "riemannXiKernel\b|riemannXiKernelTerm|riemannXiKernel_neg|riemannXiKernel_measurable|xiKernelMajorant" \
   RequestProject/XiKernelThetaBridge.lean
rg -n "riemannXiKernel_neg|riemannXiKernel_measurable|riemannXiKernel_pos_all|theorem integral_comp_abs" \
   RequestProject/*.lean tmp/c3b5_A1.lean \
   .lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/Integral.lean
rg -n "gY|sinh" tmp/c3b9_A3.lean
rg -n "def gY|gY " RequestProject/WeightedTailPrimitive.lean tmp/c3b4_A2.lean tmp/c3b4_A4.lean tmp/c3b4_A5.lean
rg -n "^namespace|^open" tmp/c3b4_A2.lean                             # → gY is CriticalLinePhasor.C3B4B.gY
rg -n "WeightedTailSinhBridge" tmp/*.lean RequestProject/*.lean       # → NOT imported anywhere; no olean
rg -n "theorem integral_comp_neg|integral_neg_eq_self|integral_comp_neg_eq_self" \
   .lake/packages/mathlib/Mathlib/MeasureTheory/ --glob '*.lean'
rg -n "prod_right_ae|prod_left_ae" .lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Prod.lean
rg -rn "Re\[.*xi.*/.*xi\]|logDeriv riemannXi|seat_sign|SeatSign|xi_logDeriv" RequestProject/*.lean
rg -n "634|batch 10|c3b10|cellDensity_cosh|autocorrelation" RH_LEDGER.md
grep -n -i "cellDensity|cell density|sinh(2yu)|Laguerre|weighted tail" \
   automorph/universal.tex automorph/hp_pencil_v2.tex automorph/grh_companion.tex   # → no hits
```

Name-variant findings worth keeping:
* `gY` is `CriticalLinePhasor.C3B4B.gY` (`tmp/c3b4_A2.lean:42`), **not**
  `CriticalLinePhasor.WeightedTail.gY`.  `RequestProject/WeightedTailSinhBridge.lean` defines a
  second `gY` in `CriticalLinePhasor.WeightedTail` but **that file is not built and not
  imported by anything** — no olean in `.lake/build/lib/lean/RequestProject/`.  A file that
  looks load-bearing and is not.
* `MeasureTheory.integral_comp_neg_eq_self` does not exist; `integral_neg_eq_self` exists only
  as a `to_additive` alias used inside Mathlib and did not resolve here.
* Mathlib LSP tooling was unavailable for part of the session (server disconnect); all Lean
  work went through `lake env lean` directly.

---

## PAPER / CHART AUDIT

`grep -i "cellDensity|cell density|sinh(2yu)|Laguerre|weighted tail"` over
`automorph/universal.tex` (9324 lines), `automorph/hp_pencil_v2.tex`, and
`automorph/grh_companion.tex` returns **no hits**.  The C3 cell-density campaign is not in
print, so nothing in this batch changes any paper claim and no paper edit is proposed.

Chart distinctions, preserved and used:

| chart | coordinate | role in batch 11 |
|---|---|---|
| native helix, `Re s > 0`, phasors entering at 0 | — | the weights `wQ,wS,wP,wR` are entire; no convergence abscissa is invoked anywhere.  The `t·e^{λt}Φ` integrability is proved by tilt-shifting, not by a half-plane. |
| carrier `Z`, `t = log Z` | `t = u+p`, `s = u−p` legs; `u` cell centre, `p` half-gap | the whole of `c3b11_A1`/`A2` lives here.  `carrier_pairing2` is a carrier statement; `bilin2` is its sheared coordinate. |
| Ξ chart `z = i(s − ½)` | — | used ONLY in the EQUIV navigation (§EQUIV step 3), never inside a locator or a definition. |
| conjugate double helix / anti-helix | `s ↦ −s` on the fibre | F5: the anti-helix branch of the leaf is *equal* to the helix branch, not opposite.  Recorded as a derived negative. |
| harmonisation scale `π/3`, not 1 | — | no scan in this batch is a unit-1 scan; the numerics are moment evaluations, not cell-registration scans, so the `π/3` register is not at risk here.  Flagged: if any later batch scans this leaf over a *cell* variable, it must be on `π/3` cells (`method-law-harmonic-scale`). |
| carrier `S(t)` registration gap | — | distinct from, and not used by, the Ξ-side `S_t` of the pencil.  Neither appears in batch 11; no blending occurred. |

`RequestProject/XiStructureFunction.lean` audit: `rh_of_xiStructure_isHB` routes RH through
Hermite–Biehler positivity of `E_ξ = ξ + ξ′`.  That is a **different** sufficient condition
from the leaf (`Re[ξ′/ξ] ≥ 0` right of the line); both are `EQUIV`-class, and the batch-11
identity does not feed the HB route.  Recorded so the two are not conflated later.

---

## GIT DIFF REVIEW

```
git diff --stat            # → EMPTY: no tracked file modified
git status --porcelain | grep -v '^?? tmp/'
?? RequestProject/WeightedTailPrimitive.lean      (pre-existing, untouched)
?? RequestProject/WeightedTailSinhBridge.lean     (pre-existing, untouched)
?? RequestProject/XiHelixChart.lean               (pre-existing, untouched)
?? RequestProject/XiStructureResidual634.lean     (pre-existing, untouched)
?? RequestProject/XiStructureSeatBridge.lean      (pre-existing, untouched)
```

New files, all under `tmp/`, all untracked, nothing committed:

```
tmp/c3b11_A1.lean  tmp/c3b11_A1.log  tmp/c3b11_A1.olean
tmp/c3b11_A2.lean  tmp/c3b11_A2.log  tmp/c3b11_A2.olean
tmp/c3b11_A3.lean  tmp/c3b11_A3.log  tmp/c3b11_A3.olean
tmp/c3b11_probe1.lean
tmp/c3b11_num.py   tmp/c3b11_num_out.txt
tmp/c3b11_num2.py  tmp/c3b11_num2_out.txt
tmp/c3b11_verify_A2.txt  tmp/c3b11_verify_A3.txt
tmp/claude_c3_proof_batch11_20260825.md   (this file)
```

`tmp/c3b10_A1.lean`, `tmp/c3b10_A2.lean`, `tmp/c3b10_A3.lean`: **byte-identical, not opened for
write.**  Their `.olean` timestamps are unchanged (Aug 25 01:23 / 01:30 / 01:33); the
re-verification runs used `lake env lean` with no `-o`.

---

## MACHINE-READABLE SUMMARY

```yaml
batch: c3-batch-11
date: 2026-08-25
target_leaf: "0 <= integral_{Ioi 0} (u * sinh(2*y*u)) * C3B6.Theta.cellDensity x u"
target_proved: false
rh_claimed: false
grh_claimed: false
commits_made: 0
tracked_files_modified: 0
c3b10_files_modified: 0
lean_files_new: 4
lean_declarations_compiled: 39
axiom_footprint_all: "[propext, Classical.choice, Quot.sound]"
sorry_admit_axiom_nativedecide_scan: clean
attacks_executed: 23
headline_theorem:
  name: C3B11.target_eq
  file: tmp/c3b11_A2.lean
  statement: "integral_{Ioi 0} gY y u * cellDensity x u = 4^{-1} * (cosMom (wQ y) x * cosMom (wP y) x + sinMom (wS y) x * sinMom (wR y) x)"
  hypotheses: "none (x y : R arbitrary)"
  removes: "differentiation under the integral sign; the oscillatory 2D integral"
enabling_theorem:
  name: C3B11.carrier_pairing2
  file: tmp/c3b11_A1.lean
  hypotheses: "Integrable P, Measurable P, Integrable Q, Measurable Q"
fibres_closed_unconditionally:
  - "x = 0, y >= 0 : C3B11.target_zero_nonneg"
  - "y = 0, all x  : C3B11.target_y_zero (exactly 0)"
open_leaf_next_lean_statement: |
  theorem leaf_sign (x : R) {y : R} (hy : 0 <= y) :
      0 <= C3B10.cosMom (C3B11.wQ y) x * C3B10.cosMom (C3B11.wP y) x
        + C3B10.sinMom (C3B11.wS y) x * C3B10.sinMom (C3B11.wR y) x
open_subleaf_next_lean_statement: |
  theorem laguerre_edge (x : R) :
      0 <= (integral t, t * riemannXiKernel t * sin (x*t))^2
        + (integral t, riemannXiKernel t * cos (x*t)) * (integral t, t^2 * riemannXiKernel t * cos (x*t))
equiv_class: "leaf <=> Re[xi'/xi] >= 0 on Re s >= 1/2 <=> RH (pencil; one uncompiled differentiation step)"
counterexamples_found: 2
counterexample_1:
  kernel: "Phi_c(t) = e^{-t^2}(2 + cos 2t), positive even Schwartz"
  transform: "M_c(z) = sqrt(pi) e^{z^2/4} (2 + e^{-1} cos z)"
  witness: "z0 = pi + i*arccosh(2e) = 3.14159265358979 + 2.37772652459815i"
  negative_sample: "Q_c(x=2.3777265246, y=3.00) = -7.19124073e+00"
  kills: "any derivation of the sign from Phi > 0 + evenness + the shear"
counterexample_2:
  kernel: "Phi_g = e^{-t^2} + e^{-4t^2}  (SINGLE EXPLICIT EXAMPLE, not a class)"
  property: "Phi_g(sqrt(.)) is completely monotone (two-atom Bernstein measure)"
  transform: "M_g(z) = sqrt(pi) e^{z^2/4} + (sqrt(pi)/2) e^{z^2/16}"
  witness: "z = 2.59435455359 + 3.22915786432i"
  negative_sample: "Q_g(x=3.229158, y=2.2052) = -1.68281720e-01"
  kills: "sufficiency of complete monotonicity of Phi(sqrt(.))"
  does_not_establish: "any statement about the class of all Gaussian mixtures; the batch-11 whole-class claim is WITHDRAWN as unproved (Hadamard order bound and entirety of M were assumed, not derived)"
corrections_applied_in_batch_12:
  - "Q/|M|^2 = d/dy log|M| = (1/2) d/dy log|M|^2 = Re[xi'/xi]; batch 11 printed '2 * d/dy log|M|' -- wrong factor 2, scan results unaffected"
  - "the x=0 hostile-scan row is a numerical limit at x=1e-6; the closed-form log-derivative has a REMOVABLE singularity at s=1 (pole of 1/(s-1) cancels pole of zeta'/zeta), and (x,y)=(0,1/2) is exactly s=1"
  - "Gaussian-mixture conclusion restricted to the explicit two-Gaussian example"
hostile_scan:
  method: "mpmath 30 dps, Q = 4|xi|^2 Re[xi'/xi] from the closed-form log-derivative"
  grid: "x = 0(0.5)150 plus 53 zero ordinates at offsets 0,+-0.001,+-0.01,+-0.05; y in 1e-6..5 (12 values)"
  pairs: 8064
  negatives: 0
  min_ratio: 4.62099862e-08
  verdict: NULL
retraction:
  what: "part-1 double-precision scan reported 15125 negatives from x~30 upward"
  status: "RETRACTED as quadrature noise; |M| falls below the 1e-12 absolute noise floor"
  evidence: "tmp/c3b11_num2_out.txt section M1"
literature_check_required:
  - "first Laguerre inequality Xi'^2 - Xi Xi'' >= 0 for the Riemann Xi function (Csordas-Norfolk-Varga adjacent); NOT read at source this session; make no status claim until read"
repo_findings:
  - "RequestProject/WeightedTailSinhBridge.lean is not built and not imported by anything (no olean); gY resolves to CriticalLinePhasor.C3B4B.gY in tmp/c3b4_A2.lean:42"
  - "MeasureTheory.integral_comp_neg_eq_self does not exist in this Mathlib"
```
