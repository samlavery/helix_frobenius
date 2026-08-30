# C3 proof batch 6 — 2026-08-24

No `RequestProject/` or `automorph/` file created or modified. No tracked file edited. No
commits (`HEAD` still `da72c64`). No Python, no numerics, no quadrature. `att542`, `att544`,
`att545` not run and not read for evidence.

**`AGENTS.md` does not exist in this repository** (`find . -iname "AGENTS*"` repo-wide,
`.git` excluded, returns nothing). `CLAUDE.md` is the governing rules file and was read in
full.

## Chart dictionary (preserved)

- Native helix: `Re s > 0`; entry wall `Re s = 0`, where phasors enter at zero magnitude.
- Xi chart: `z = i(s − 1/2)`, so `Re z = −Im s` (ordinate) and `Im z = Re s − 1/2` (depth).
- `E` and `E*` are the conjugate double helix / anti-helix pair; chart conjugation is the
  functional-equation reflection `s ↦ 1 − conj s`.
- Carrier chart: physical height `Z`, analytic ordinate `t = log Z`.
- Native harmonized readout `N_{π/3}(e^t)`; unit-1 *scalar receiver* `R_1(e^t) = 1 + θ(t)/π`.
- Registration gap `S(t) = N_{π/3}(e^t) − R_1(e^t)`. Unit 1 is the comparison receiver,
  never the native carrier.
- Carrier-scale `S(t)`, Xi-chart `z`, and Hermitian pencil `S_t` are three distinct objects.
- Distinct-event line, multiplicity line, and classical strip ledgers stay typed separately
  (`S_class = S_mult + N_off^mult`, `S_mult = S_ev + excess line multiplicity`).

Mode-level reading of the same geometry, new this batch: the involution `(n,m) ↦ (m,n)` is
the double-helix/anti-helix exchange `a/b ↦ b/a` on the theta mode pairs; the two
contributions are **equal** because the arithmetic phase is even
(`C3B6.Theta.modePair_integral_symm`), so the double sum carries no sine part.

---

# COMPILE RECORD

Ten files, all `EXIT=0`, `0` errors, **106** `#print axioms` lines, every one exactly
`[propext, Classical.choice, Quot.sound]`. Escape-hatch scan
(`sorry|admit|^axiom |native_decide|unsafe|implemented_by`) over all ten: **0 hits**.

| file | first literal line | EXIT | errors | axiom prints | standard | escape hatches |
|---|---|---|---|---|---|---|
| `tmp/c3b6_A1.lean` | `import Mathlib` | 0 | 0 | 7 | 7 | 0 |
| `tmp/c3b6_A2.lean` | `import c3b6_A1` | 0 | 0 | 14 | 14 | 0 |
| `tmp/c3b6_A3.lean` | `import c3b6_A2` | 0 | 0 | 9 | 9 | 0 |
| `tmp/c3b6_A4.lean` | `import c3b6_A3` | 0 | 0 | 9 | 9 | 0 |
| `tmp/c3b6_A5.lean` | `import c3b6_A4` | 0 | 0 | 16 | 16 | 0 |
| `tmp/c3b6_A6.lean` | `import c3b6_A5` | 0 | 0 | 10 | 10 | 0 |
| `tmp/c3b6_A7.lean` | `import c3b6_A6` | 0 | 0 | 12 | 12 | 0 |
| `tmp/c3b6_A8.lean` | `import c3b6_A7` | 0 | 0 | 9 | 9 | 0 |
| `tmp/c3b6_A9.lean` | `import c3b6_A8` | 0 | 0 | 9 | 9 | 0 |
| `tmp/c3b6_A10.lean` | `import c3b6_A9` | 0 | 0 | 12 | 12 | 0 |

Reproduce from repo root:

```
lake env lean -o tmp/c3b5_A1.olean tmp/c3b5_A1.lean
lake env lean -o tmp/c3b5_A2.olean tmp/c3b5_A2.lean
lake env lean -o tmp/c3b5_A3.olean tmp/c3b5_A3.lean
lake env lean -o tmp/c3b6_A1.olean tmp/c3b6_A1.lean
export LP="$(lake env printenv LEAN_PATH):$PWD/tmp"
for k in 2 3 4 5 6 7 8 9; do
  LEAN_PATH="$LP" lake env lean -o tmp/c3b6_A$k.olean tmp/c3b6_A$k.lean
done
LEAN_PATH="$LP" lake env lean tmp/c3b6_A10.lean
```

Verbatim axiom output, headline theorems (from `tmp/c3b6_A*.log`):

```
'C3B6.Bessel.kix_bessel_ode' depends on axioms: [propext, Classical.choice, Quot.sound]
'C3B6.Bessel.logDeriv_kix_le_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'C3B6.Bessel.radial_kix_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'C3B6.Bessel.kix_zero_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'C3B6.Bessel.radial_kix_pos_uncond' depends on axioms: [propext, Classical.choice, Quot.sound]
'C3B6.Bessel.radial_kix_pos_at' depends on axioms: [propext, Classical.choice, Quot.sound]
'C3B6.Theta.modePair_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'C3B6.Theta.modePair_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
'C3B6.Theta.summable_modeBound' depends on axioms: [propext, Classical.choice, Quot.sound]
'C3B6.Theta.modePair_integral_abs_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'C3B6.Theta.headMode_integral_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'C3B6.Theta.kernel_product_tsum' depends on axioms: [propext, Classical.choice, Quot.sound]
'C3B6.Theta.C_tsum' depends on axioms: [propext, Classical.choice, Quot.sound]
'C3B6.Theta.cellDensity_eq_tsum' depends on axioms: [propext, Classical.choice, Quot.sound]
'C3B6.Theta.cellDensity_pos_of_head_dominant' depends on axioms: [propext, Classical.choice, Quot.sound]
'C3B6.Theta.UTail_nonneg_of_cellDensity_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'C3B6.Theta.kixConst_le' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## SEARCH RECORD (obligation D), read at source before constructing

Mathlib, nine naming variants — `Bessel`, `besselJ`, `besselK`, `Macdonald`,
`modifiedBessel`, `cylinderFunction`, `Kelvin`, `hankel`, `Hankel`: **no Bessel function of
any kind is defined in Mathlib.** The only `Macdonald` hits are Atiyah–Macdonald citations
in `RingTheory/Lasker.lean`.

Repository, six variants — `Bessel`, `besselKix`, `Kix`, `macdonald`, `Real.cosh`,
`exp (-A * Real.cosh`: the only hit is `RequestProject/BesselOrderLadder.lean`, whose
`cosKernel n z = ∫_0^π cos(nθ)e^{−iz cos θ}dθ` is the **integer-order** cosine channel
(classically `J_n`) on a compact interval. Not `K_{ix}`; does not specialize to it.

Also searched at source and used rather than reconstructed:
`MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto'`,
`hasDerivAt_integral_of_dominated_loc_of_deriv_le`, `integrable_exp_neg_mul_sq`,
`exp_neg_integrableOn_Ioi`, `Real.one_sub_sq_div_two_le_cos`,
`Real.quadratic_le_exp_of_nonneg`, `Real.pow_div_factorial_le_exp`, `Real.exp_one_lt_d9`,
`Summable.mul_of_nonneg`, `Real.summable_pow_mul_exp_neg_nat_mul`,
`tsum_mul_tsum_of_summable_norm`, `MeasureTheory.integral_tsum_of_summable_integral_norm`,
`Summable.tsum_eq_add_tsum_ite`, `MeasureTheory.Measure.integral_comp_mul_left`,
`MeasureTheory.integral_add_right_eq_self`, `integral_comp_neg_Iic`,
`intervalIntegral.integral_Iic_add_Ioi`.

---

# COMPILED — exact statements

## A1 — `tmp/c3b6_A1.lean` — the Macdonald function of imaginary order, constructed

```
kixTerm (j : ℕ) (x A w : ℝ) : ℝ := (-Real.cosh w)^j * Real.exp (-(A * Real.cosh w)) * Real.cos (x*w)
kix     (j : ℕ) (x A   : ℝ) : ℝ := ∫ w in Set.Ioi (0:ℝ), kixTerm j x A w
besselKix (x A : ℝ) : ℝ := kix 0 x A
coshMaj (j : ℕ) (δ w : ℝ) : ℝ := Real.exp (-(δ/2)) * Real.exp (((j:ℝ) - δ/2)*w - (δ/4)*w^2)
kixConst (j : ℕ) (δ : ℝ) : ℝ := ∫ w in Set.Ioi (0:ℝ), coshMaj j δ w
```

| # | theorem | exact statement |
|---|---|---|
| 1 | `exp_div_two_le_cosh` | `∀ w, Real.exp w / 2 ≤ Real.cosh w` |
| 2 | `cosh_le_exp` | `0 ≤ w → Real.cosh w ≤ Real.exp w` |
| 3 | `quad_le_two_cosh` | `0 ≤ w → 1 + w + w^2/2 ≤ 2 * Real.cosh w` |
| 4 | `cosh_pow_exp_le` | `0 < δ → δ ≤ A → 0 ≤ w → cosh w ^ j * exp (-(A*cosh w)) ≤ coshMaj j δ w` |
| 5 | `kixTerm_abs_le_cosh` | `∀ j x A w, \|kixTerm j x A w\| ≤ cosh w ^ j * exp (-(A*cosh w))` |
| 6 | `kixTerm_abs_le` | `0 < δ → δ ≤ A → 0 ≤ w → \|kixTerm j x A w\| ≤ coshMaj j δ w` |
| 7 | `coshMaj_integrable` | `0 < δ → Integrable (coshMaj j δ)` |
| 8 | `kixTerm_integrableOn` | `0 < A → IntegrableOn (kixTerm j x A) (Ioi 0)` |
| 9 | `kix_abs_le` | `0 < δ → δ ≤ A → \|kix j x A\| ≤ Real.exp (-(A - δ)) * kixConst j δ` |

## A2 — `tmp/c3b6_A2.lean` — **the modified-Bessel ODE, proved**

| # | theorem | exact statement |
|---|---|---|
| 10 | `abs_sinh_le_cosh` | `∀ w, \|Real.sinh w\| ≤ Real.cosh w` |
| 11 | `coshMaj_tendsto_zero` | `0 < δ → Tendsto (coshMaj j δ) atTop (nhds 0)` |
| 12 | `hasDerivAt_kixTerm` | `HasDerivAt (fun a => kixTerm j x a w) (kixTerm (j+1) x A w) A` |
| 13 | `hasDerivAt_kix` | `0 < A → HasDerivAt (kix j x) (kix (j+1) x A) A` |
| 14 | `hasDerivAt_gFun` | `HasDerivAt (gFun A) (gDer A w) w`, `gFun A w = −sinh w·e^{−A cosh w}` |
| 15 | `hasDerivAt_eFun` | `HasDerivAt (eFun A) (A * gFun A w) w` |
| 16 | `integrableOn_gFun_sin`, `integrableOn_eFun_cos`, `integrableOn_gDer_cos` | integrability of the three IBP integrands on `Ioi 0` |
| 17 | `tendsto_gFun_cos`, `tendsto_eFun_sin` | both boundary profiles `→ 0` at `+∞` |
| 18 | `ibp_one` | `0 < A → ∫_{Ioi 0} gDer A w·cos(xw) = x · ∫_{Ioi 0} gFun A w·sin(xw)` |
| 19 | `ibp_two` | `0 < A → A · ∫_{Ioi 0} gFun A w·sin(xw) = −(x · kix 0 x A)` |
| 20 | `combo_pointwise` | `A·kixTerm 2 + kixTerm 1 − A·kixTerm 0 = gDer A w · cos(xw)` |
| 21 | `combo_integral` | `0 < A → A·kix 2 + kix 1 − A·kix 0 = ∫_{Ioi 0} gDer A w·cos(xw)` |
| **22** | **`kix_bessel_ode`** | **`0 < A → A^2 * kix 2 x A + A * kix 1 x A − (A^2 − x^2) * kix 0 x A = 0`** |
| 23 | `deriv_kix` | `0 < A → deriv (kix j x) A = kix (j+1) x A` |

Both integrations by parts are `MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto'`, with
`gFun A 0 = 0` and `eFun A 0 · sin 0 = 0` killing the finite boundary terms and
`coshMaj_tendsto_zero` killing the ones at `+∞`. No asymptotics, no series, no analytic
continuation, no Watson's lemma.

## A3 — `tmp/c3b6_A3.lean` — obligation A, with one value hypothesis

```
zFun x A = Real.sqrt A * kix 0 x A
zDer x A = 1/(2*Real.sqrt A) * kix 0 x A + Real.sqrt A * kix 1 x A
zDD  x A = -(1/(4*(Real.sqrt A)^3)) * kix 0 x A + 1/Real.sqrt A * kix 1 x A + Real.sqrt A * kix 2 x A
qFun x A = 1 - (x^2 + 1/4)/A^2
```

| # | theorem | exact statement |
|---|---|---|
| 24 | `qFun_le_one` | `∀ x A, qFun x A ≤ 1` |
| 25 | `hasDerivAt_zFun` | `0 < A → HasDerivAt (zFun x) (zDer x A) A` |
| 26 | `hasDerivAt_invSqrt` | `0 < A → HasDerivAt (fun t => 1/(2*√t)) (−(1/(4*(√A)^3))) A` |
| 27 | `hasDerivAt_zDer` | `0 < A → HasDerivAt (zDer x) (zDD x A) A` |
| 28 | `zDD_eq` | `0 < A → zDD x A = qFun x A * zFun x A` (via `C3B5.A3.liouville_normal_form` at `r = √A`) |
| 29 | `tendsto_zSum` | `Tendsto (fun A => zFun x A + zDer x A) atTop (nhds 0)` |
| 30 | `logDeriv_kix_le_one` | `0 < a → (∀ A ∈ Ici a, 0 < kix 0 x A) → ∀ A ∈ Ici a, −zDer x A / zFun x A ≤ 1` |
| 31 | `kix_logDeriv_transfer` | `0 < A → kix 0 x A ≠ 0 → kix 1 x A = −((−zDer x A/zFun x A) + 1/(2*A)) * kix 0 x A` |
| **32** | **`radial_kix_pos`** | **`8 ≤ a → (∀ A ∈ Ici a, 0 < kix 0 x A) → ∀ A ∈ Ici a, 0 < (A^2+9)*kix 0 x A + 6*A*kix 1 x A`** |

`C3B5.A3.logDeriv_le_one` is *applied*, not restated; `C3B5.A2.radial_pos_of_ge_eight` is
*composed with*. The derivative inequality `ρ ≤ 1` is a **conclusion** (#30), never a
hypothesis.

## A4 — `tmp/c3b6_A4.lean` — obligation A, **hypothesis-free**

| # | theorem | exact statement |
|---|---|---|
| 33 | `kixTerm_zero_eq` | `kixTerm 0 x A w = exp(−(A cosh w))·cos(xw)` |
| 34 | `cosh_le_cosh_of_le` | `0 ≤ w → w ≤ h → cosh w ≤ cosh h` |
| 35 | `half_le_sinh` | `0 ≤ h → h/2 ≤ Real.sinh h` |
| 36 | `cosh_tangent_lower` | `0 ≤ h → h ≤ w → cosh h + sinh h·(w−h) ≤ cosh w` |
| 37 | `integral_exp_neg_shift` | `0 < c → ∫_{Ioi h} exp(−(c(w−h))) = 1/c` |
| 38 | `kix_head_ge` | `0 < A → 0 < h → \|x\|·h ≤ 1 → exp(−(A cosh h))·(1/2)·h ≤ ∫_{Ioc 0 h} kixTerm 0 x A` |
| 39 | `kix_tail_abs_le` | `0 < A → 0 < h → \|∫_{Ioi h} kixTerm 0 x A\| ≤ exp(−(A cosh h))·(1/(A sinh h))` |
| **40** | **`kix_zero_pos`** | **`4*(\|x\|+1)^2 < A → 0 < kix 0 x A`** |
| **41** | **`radial_kix_pos_uncond`** | **`8 ≤ a → 4*(\|x\|+1)^2 < a → ∀ A ∈ Ici a, 0 < (A^2+9)*kix 0 x A + 6*A*kix 1 x A`** |
| 42 | `radial_kix_pos_at` | `8 ≤ A → 4*(\|x\|+1)^2 < A → 0 < (A^2+9)*kix 0 x A + 6*A*kix 1 x A` |

**Honest scope on #40.** The true turning point is `A > √(x²+¼)`, linear in `x`. The proved
threshold is `A > 4(|x|+1)²`, quadratic. The gap is the price of a proof using only the
first lobe of `cos` and the tangent-line convexity of `cosh`; recorded, not hidden.
Downstream, the compact window it leaves is `[0, ½log(4(x+1)²/2π)]` rather than
`[0, ½log(x/2π)]`.

## A5 — `tmp/c3b6_A5.lean` — the exact `(n,m)` cross term

```
modeA (n m : ℕ) (u : ℝ) : ℝ := 2*Real.pi*((n:ℝ)+1)*((m:ℝ)+1)*Real.exp (2*u)
modeW (n m : ℕ) (p : ℝ) : ℝ := 2*p + Real.log (((n:ℝ)+1)/((m:ℝ)+1))
modeLam (n m : ℕ) : ℝ := Real.log (((n:ℝ)+1)/((m:ℝ)+1))
kixTermShift (j : ℕ) (x A lam w : ℝ) : ℝ := (-Real.cosh w)^j * Real.exp (-(A*Real.cosh w)) * Real.cos (x*(w - lam))
modeIntegrandW (n m : ℕ) (x u w : ℝ) : ℝ :=
  (modeA n m u ^ 2 + 9) * kixTermShift 0 x (modeA n m u) (modeLam n m) w
    + 6 * modeA n m u * kixTermShift 1 x (modeA n m u) (modeLam n m) w
```

| # | theorem | exact statement |
|---|---|---|
| 43 | `integrable_exp_lin_quad` | `0 < b → Integrable (fun w => exp (c*w − b*w^2))` |
| 44 | `cosh_pow_exp_le_two` | `0 < δ → δ ≤ A → cosh w ^ j * exp(−(A cosh w)) ≤ coshMajTwo j δ w` (**every** real `w`) |
| 45 | `coshMajTwo_integrable`, `kixLike_integrable`, `kixTerm_integrable` | full-line integrability |
| 46 | `kixTerm_even`, `kixFull_eq` | `∫_ℝ kixTerm j x A = 2 * kix j x A` |
| 47 | `kixTermSin_odd`, `integral_kixTermSin` | `∫_ℝ kixTermSin j x A = 0` |
| 48 | `integral_kixTermShift` | `0 < A → ∫_ℝ kixTermShift j x A lam = 2 * cos (x*lam) * kix j x A` |
| 49 | `modeA_exp_w`, `modeA_exp_neg_w` | `A·e^{±w}` are the two polynomial arguments, exactly |
| 50 | `kernelTerm_factor` | `riemannXiKernelTerm n t = π a² e^{5t/2}(2π a² e^{2t} − 3)e^{−π a² e^{2t}}` |
| **51** | **`modePair_eq`** | **`Φ_n(u+p)·Φ_m(u−p) = π²(n+1)²(m+1)²·e^{5u}·(A²−6A cosh w+9)·e^{−A cosh w}`** |
| 52 | `modeIntegrandW_eq` | the bracket-times-shifted-cosine IS the two-term linear combination |
| **53** | **`modePair_integral`** | **`∫_ℝ Φ_n(u+p)Φ_m(u−p)cos(2xp)dp = π²(n+1)²(m+1)²e^{5u}·cos(x·modeLam n m)·C3B5.A2.radial (modeA n m u) (kix 0 x (modeA n m u)) (kix 1 x (modeA n m u))`** |
| 54 | `modeA_eq_of_prod_eq`, `modePair_weight`, `modePair_phase` | the hyperbola collapse: `A_{nm}` sees only `ab`; `a²b² = (ab)²`; `cos(x log(a/b)) = cos(x log(a²/k))` for `ab = k` |

`C3B5.A1.theta_pair_cosh` and `C3B5.A1.bracket_product` are here **applied to the
repository's actual `riemannXiKernelTerm`**, not to an abstract pair.

## A6 — `tmp/c3b6_A6.lean` — explicit mode bounds and the summable majorant

```
modeBound (x u : ℝ) (q : ℕ × ℕ) : ℝ :=
  Real.pi^2 * (((q.1:ℝ)+1)*((q.2:ℝ)+1))^2 * Real.exp (5*u)
    * (((modeA q.1 q.2 u)^2 + 9) * kixConst 0 (modeA 0 0 u)
        + 6*(modeA q.1 q.2 u) * kixConst 1 (modeA 0 0 u))
    * Real.exp (-(modeA q.1 q.2 u - modeA 0 0 u))
```

| # | theorem | exact statement |
|---|---|---|
| **55** | **`kix_zero_lower`** | **`8*(\|x\|+1)^2 ≤ A → exp(−(A·cosh(1/(\|x\|+1))))·(1/(\|x\|+1))/4 ≤ kix 0 x A`** |
| **56** | **`radial_abs_le`** | **`0 < δ → δ ≤ A → \|C3B5.A2.radial A (kix 0 x A) (kix 1 x A)\| ≤ ((A^2+9)·kixConst 0 δ + 6A·kixConst 1 δ)·exp(−(A−δ))`** |
| 57 | `cosh_one_lt_two`, `cosh_lt_two_of_le_one` | `0 ≤ h → h ≤ 1 → cosh h < 2` — the head-vs-tail rate gap |
| 58 | `modeA_factor`, `modeA_ge_head`, `modeA_two_le` | `modeA n m u = ab·modeA 0 0 u`; `≥ modeA 0 0 u`; `≥ 2·modeA 0 0 u` off the head |
| 59 | `prod_ge_half_sum` | `1 ≤ a → 1 ≤ b → (a+b)/2 ≤ a*b` — the hyperbola inequality |
| 60 | `summable_pow_exp_shift` | `0 < c → Summable (fun n : ℕ => ((n:ℝ)+1)^k * exp(−c*((n:ℝ)+1)))` |
| **61** | **`summable_modeBound`** | **`Summable (modeBound x u)` over `ℕ × ℕ`** |

## A7 — `tmp/c3b6_A7.lean` — head positivity, remainder bound, obligation-C decompositions

```
modeThreshold (x : ℝ) : ℝ := max 8 (4*(|x|+1)^2 + 1)
```

| # | theorem | exact statement |
|---|---|---|
| **62** | **`radial_mode_pos`** | **`modeThreshold x ≤ modeA 0 0 u → ∀ n m, 0 < C3B5.A2.radial (modeA n m u) (kix 0 x (modeA n m u)) (kix 1 x (modeA n m u))`** — one threshold on the head controls *every* mode |
| 63 | `modeLam_head`, `headMode_integral` | `modeLam 0 0 = 0`; head integral `= π²e^{5u}·radial(modeA 0 0 u)` |
| **64** | **`headMode_integral_pos`** | **`modeThreshold x ≤ modeA 0 0 u → 0 < ∫_ℝ Φ_1(u+p)Φ_1(u−p)cos(2xp)dp`** |
| **65** | **`modePair_integral_abs_le`** | **`\|∫_ℝ Φ_n(u+p)Φ_m(u−p)cos(2xp)dp\| ≤ modeBound x u (n,m)`** — the proved remainder bound, termwise, no truncation |
| 66 | `modeA_symm`, `modeLam_symm` | `modeA n m u = modeA m n u`; `modeLam m n = −modeLam n m` |
| **67** | **`modePair_integral_symm`** | **the conjugate mode pairing: `(n,m)` and `(m,n)` contribute equally** |
| 68 | `ramp_tail_nonneg`, `ramp_tail_nonneg_of_mode` | quadratic ramp against a profile positive above the threshold |
| **69** | **`exp_hankel_minor_neg`** | **`0 < A₁ → ξ ≠ 0 → exp(−(A₁·exp 0))·exp(−(A₁·exp(2ξ))) < exp(−(A₁·exp ξ))^2`** |
| 70 | `neg_exp_strict_concave` | the strict midpoint concavity of `t ↦ −A₁e^t` behind #69 |

## A8 — `tmp/c3b6_A8.lean` — the complete theta double sum, pointwise

| # | theorem | exact statement |
|---|---|---|
| 71 | `kernelTerm_q_form` | `riemannXiKernelTerm n t = exp(t/2)·(2q² − 3q)·exp(−q)`, `q = xiKernelQ n t` |
| 72 | `xiKernelQ_pos`, `xiKernelQ_ge` | `0 < q`; `π e^{2t}(n+1) ≤ q` |
| 73 | `q_le_two_exp`, `q_sq_le_eight_exp` | `q ≤ 2e^{q/2}`; `q² ≤ 8e^{q/2}` |
| 74 | `kernelTerm_abs_le_exp` | `\|riemannXiKernelTerm n t\| ≤ 22·exp(t/2)·exp(−q/2)`, every real `t` |
| **75** | **`summable_kernelTerm_norm`** | **`∀ t : ℝ, Summable (fun n => ‖riemannXiKernelTerm n t‖)`** |
| **76** | **`kernel_product_tsum`** | **`Φ(u+p)·Φ(u−p) = 16·∑' z : ℕ×ℕ, Φ_{z.1}(u+p)·Φ_{z.2}(u−p)`** |
| 77 | `kernel_product_cos_tsum`, `summable_crossTerm_norm` | the same with the outer cosine inside; absolute summability at fixed `p` |

## A9 — `tmp/c3b6_A9.lean` — **the sum/integral interchange, discharged**

| # | theorem | exact statement |
|---|---|---|
| 78 | `coshMoment j A` | `∫_{Ioi 0} cosh^j w · exp(−(A cosh w))` |
| 79 | `coshMoment_le` | `0 < δ → δ ≤ A → coshMoment j A ≤ exp(−(A−δ))·kixConst j δ` |
| 80 | `coshMoment_full` | `0 < A → ∫_ℝ cosh^j w exp(−(A cosh w)) = 2·coshMoment j A` |
| 81 | `kixTermShift_abs_le_cosh`, `modeIntegrandW_abs_le`, `modeIntegrandW_integrable` | bounds and integrability of the `w`-integrand |
| 82 | `crossTerm_eq`, `crossTerm_integrable` | the cross term is `C_{nm}·modeIntegrandW(2p+λ)`, integrable in `p` |
| **83** | **`crossTerm_integral_norm_le`** | **`∫_ℝ ‖Φ_n(u+p)Φ_m(u−p)cos(2xp)‖ dp ≤ modeBound x u (n,m)`** — the `1/2` from the change of variables and the `2` from evenness cancel exactly |
| 84 | `summable_crossTerm_integral_norm` | `Summable (fun z : ℕ×ℕ => ∫_ℝ ‖…‖)` |
| **85** | **`C_tsum`** | **`∫_ℝ Φ(u+p)Φ(u−p)cos(2xp)dp = 16·∑' z : ℕ×ℕ, π²(z.1+1)²(z.2+1)²e^{5u}·cos(x·modeLam z.1 z.2)·radial(modeA z.1 z.2 u)`** |

## A10 — `tmp/c3b6_A10.lean` — the cumulative-tail bridge

```
cellDensity (x u : ℝ) : ℝ := ∫ p : ℝ, riemannXiKernel (u+p) * riemannXiKernel (u-p) * Real.cos (2*x*p)
modeTerm (x u : ℝ) (z : ℕ × ℕ) : ℝ := π²(z.1+1)²(z.2+1)²e^{5u}·cos(x·modeLam z.1 z.2)·radial(modeA z.1 z.2 u)
UTail (x s : ℝ) : ℝ := ∫ u in Ioi s, (u - s)^2/2 * cellDensity x u
```

| # | theorem | exact statement |
|---|---|---|
| 86 | `modeTerm_eq_integral`, `modeTerm_abs_le`, `summable_modeTerm` | the mode is the integral; bounded by `modeBound`; summable |
| **87** | **`cellDensity_eq_tsum`** | **`cellDensity x u = 16 * ∑' z : ℕ×ℕ, modeTerm x u z`** |
| 88 | `modeTerm_head`, `modeTerm_head_pos` | head mode exact; `modeThreshold x ≤ modeA 0 0 u → 0 < modeTerm x u (0,0)` |
| **89** | **`tsum_pos_of_head_dominant'`** | head dominance at an **arbitrary** index type (the `ℕ`-indexed `C3B5.A2.tsum_pos_of_head_dominant` cannot see the `ℕ×ℕ` head) |
| **90** | **`cellDensity_pos_of_head_dominant`** | **`(∑' z, if z = (0,0) then 0 else modeBound x u z) < modeTerm x u (0,0) → 0 < cellDensity x u`** |
| **91** | **`UTail_nonneg_of_cellDensity_nonneg`** | **`(∀ u ∈ Ioi s, 0 ≤ cellDensity x u) → 0 ≤ UTail x s`** |
| 92 | `UTail_nonneg_of_head_dominant` | head dominance at every height above `s` ⟹ `0 ≤ UTail x s` |
| 93 | `exp_quarter_sq_integral_le` | `0 < A → ∫_{Ioi 0} exp(−(A/4)w²) ≤ 1 + 4/A` (no Gaussian integral used) |
| **94** | **`kixConst_le`** | **`0 < δ → 2j ≤ δ → kixConst j δ ≤ exp(−(δ/2))·(1 + 4/δ)`** |

---

# ATTACK LEDGER — 39 exact attacks

| # | attack | outcome |
|---|---|---|
| 1 | Import a Macdonald function from Mathlib | **FAILED** — none exists (9 variants, at source) |
| 2 | Reuse `RequestProject/BesselOrderLadder.cosKernel` as `K_{ix}` | **FAILED** — integer-order `J_n` channel on `[0,π]`; wrong order type and domain |
| 3 | Define `K_{ix}` by the half-line integral | **COMPILED** (A1) |
| 4 | Gaussian majorant `cosh^j w e^{−δ cosh w} ≤ e^{−δ/2}exp((j−δ/2)w−(δ/4)w²)` | **COMPILED** (A1 #4,#7) |
| 5 | Exponential-decay bound `\|kix j x A\| ≤ e^{−(A−δ)}·kixConst j δ` | **COMPILED** (A1 #9) |
| 6 | Differentiate under the integral (dominated, ball `A' > A/2`) | **COMPILED** (A2 #13) |
| 7 | ODE by **two IBPs on `(0,∞)`** with vanishing boundary terms | **COMPILED** (A2 #22) |
| 8 | Alt to #7: `ρ ≤ 1` directly from the integral rep, no ODE | **ABANDONED before Lean** — `(1+1/(2A))K + K′ = ∫[(1+1/(2A)) − cosh w]e^{−A cosh w}cos(xw)dw` has a sign-indefinite bracket against an oscillating `cos(xw)`; no pointwise sign argument exists |
| 9 | Alt to #7: substitution `cosh w − 1 = σ²/(2A)` making `e^A z` a Gaussian average | **ABANDONED before Lean** — the limit `∫_0^∞ e^{−σ²/2}cos(x·w(σ/√A))dσ` is monotone in neither factor; `cos(xw)` is not monotone as `w ↓ 0` |
| 10 | Liouville gauge `z = √A K`, `z″ = qz` | **COMPILED** (A3 #28) |
| 11 | Boundary `z + z′ → 0` from the A1 decay bound | **COMPILED** (A3 #29) |
| 12 | Conclude `ρ ≤ 1` by `C3B5.A3.logDeriv_le_one` | **COMPILED** (A3 #30) |
| 13 | Compose with `C3B5.A2.radial_pos_of_ge_eight` | **COMPILED** (A3 #32) |
| 14 | `K_{ix} > 0` by first lobe + tangent-line tail split | **COMPILED** (A4 #40) at `A > 4(\|x\|+1)²` |
| 15 | Alt to #14: `K = (A/x)e^{−A}∫_0^∞ e^{−At}sin(x·arccosh(1+t))dt`, first-lobe Laplace | **ABANDONED before Lean** — the first positive lobe has length `≈ π²/(2x²)`, so domination needs `A ≳ x²·log x`, strictly worse than #14 |
| 16 | Alt to #14: Sturm `E = z′² − qz²` monotone (`E′ = −q′z² ≤ 0`, `E → 0` ⟹ `E ≥ 0`) | **ABANDONED before Lean** — closes only "no *double* zero"; excluding a simple zero still needs "`K ≠ 0` far out", i.e. #14 or Watson's lemma. Recorded as the sharper route if the linear threshold `A > √(x²+¼)` is ever needed |
| 17 | Exact `(n,m)` cross term, `C3B5.A1` lemmas applied to the repo kernel | **COMPILED** (A5 #51) |
| 18 | Full-line integrability, evenness/oddness of the Macdonald integrands | **COMPILED** (A5 #44–#47) |
| 19 | Shifted-cosine evaluation `∫_ℝ = 2cos(xλ)·kix` (sine half odd, dies) | **COMPILED** (A5 #48) |
| 20 | `p`-integral change of variables `w = 2p + λ` | **COMPILED** (A5 #53) |
| 21 | Quantitative lower bound `kix_zero_lower` | **COMPILED** (A6 #55) |
| 22 | Explicit upper bound `radial_abs_le` (no log-derivative used, so valid below the turning point too) | **COMPILED** (A6 #56) |
| 23 | Hyperbola inequality `ab ≥ (a+b)/2` → product-of-two-families summable majorant over `ℕ×ℕ` | **COMPILED** (A6 #59,#61) |
| 24 | `cosh 1 < 2`: the head rate `e^{−A₁cosh h}` beats every off-head rate `e^{−2A₁}` | **COMPILED** (A6 #57) |
| 25 | Uniform mode positivity from one head threshold | **COMPILED** (A7 #62) |
| 26 | `(1,1)` mode exact and strictly positive | **COMPILED** (A7 #63,#64) |
| 27 | Proved remainder bound for every other mode | **COMPILED** (A7 #65) |
| 28 | Conjugate mode pairing `(n,m) ↔ (m,n)` (obligation C: π/3-native phase pairing) | **COMPILED** (A7 #67) — contributions are **equal**, so no sine part survives |
| 29 | Ramp/IBP against a positive kernel (obligation C) | **COMPILED** (A7 #68) |
| 30 | Total positivity after an admissible transform (obligation C) | **REFUTED, at the actual parameter** (A7 #69) — the multiplicative Hankel kernel's leading factor `e^{−A₁e^t}` is log-*concave*, so Widder's exponential-convexity criterion fails for every `A₁ > 0`, `ξ ≠ 0`. Upgrades `C3B5.A4.exp_exp_hankel_minor_neg` from the model `A₁ = 1` to `A₁ = 2πe^{2u}` |
| 31 | Pointwise complete theta double sum (absolute summability at every real `t`) | **COMPILED** (A8 #75,#76) |
| 32 | Sum/integral interchange via `integral_tsum_of_summable_integral_norm` | **COMPILED** (A9 #85) |
| 33 | Head-dominance criterion at a general index type | **COMPILED** (A10 #89) |
| 34 | Cumulative-tail bridge `UTail` | **COMPILED** (A10 #91) |
| 35 | Gaussian-free elementary bound `∫_0^∞ e^{−Aw²/4} ≤ 1 + 4/A` | **COMPILED** (A10 #93) |
| 36 | Explicit mode constant `kixConst j δ ≤ e^{−δ/2}(1 + 4/δ)` | **COMPILED** (A10 #94) |
| 37 | Uniform linear ramp `T(r,x) ≥ 0` | **FAILED**, carried, **not retried** — `T(0,60) = −2.4411414711711282366e−36` |
| 38 | Fixed-`d` J-kernel fiber positivity | **FAILED**, carried, **not retried** — does not control the outer `cos(xd)` |
| 39 | `rampKernel(a+b) = max(a+b,0)²` PSD; generic Hankel-square factorization | **FAILED**, carried — `C3B5.A4.rampKernel_not_psd` (value `−4`), `C3B5.A4.exp_exp_hankel_minor_neg` |

Errors actually hit and fixed (compiler-guided, not guessed):
`pow_le_pow_left` → `pow_le_pow_left₀`; `abs_add` → `abs_add_le`;
`integral_Iic_add_Ioi` → `intervalIntegral.integral_Iic_add_Ioi`;
`integrableOn_const` is no longer an iff (autoparam `μ s ≠ ∞`);
`setIntegral_const` now yields `volume.real s • c`, so `Real.volume_real_Ioc_of_le` replaces
`Real.volume_Ioc` + `ENNReal.toReal_ofReal`;
`simpa` rewrites `fun x => -f x` into the `Pi` negation `-f`, breaking `HasDerivAt`
unification — every such site was rewritten to `congr_deriv` with an explicit `ring`;
`Pi.inv_apply` needed explicitly for `(fun t => 2*√t)⁻¹`.
A genuine mathematical error caught by the compiler: the first draft of `kix_zero_lower`
derived `8/h ≤ A·h` and then needed `4 ≤ h·(A·sinh h)`, which that form does **not** give
(it yields `≥ 4h`, and `h ≤ 1`); the correct intermediate is `8 ≤ A·h²`.

---

# OPEN — with citations

1. **The head-dominance inequality** — the one Prop-valued input of
   `cellDensity_pos_of_head_dominant` (A10 #90):
   `(∑' z : ℕ×ℕ, if z = (0,0) then 0 else modeBound x u z) < modeTerm x u (0,0)`.
   Every ingredient for it is now compiled: the head lower bound (A6 #55 + `C3B5.A2.radial_ge`),
   the termwise majorant (A7 #65), its summability (A6 #61), the rate gap `cosh h < 2 ≤` every
   off-head rate (A6 #57, #58), and the explicit constant `kixConst j δ ≤ e^{−δ/2}(1+4/δ)`
   (A10 #94). What is missing is the *arithmetic*: an explicit closed upper bound for
   `∑_{ab≥2} (ab)²[((ab·A₁)²+9)C₀ + 6(ab)A₁C₁] e^{−(ab−1)A₁}` compared against
   `(A₁²−6A₁+6)·e^{−A₁cosh h}·h/4`.
2. `U_x(s) ≥ 0` for all `s ≥ 0` — batch-4 attack 23, batch-5 §OPEN. The bridge
   `UTail_nonneg_of_cellDensity_nonneg` (A10 #91) now reduces it to `cellDensity ≥ 0` on
   `(s,∞)`, which item 1 supplies above an explicit height. The **compact window**
   `[0, u₁(x)]` with `2πe^{2u₁} = modeThreshold x` remains untouched.
3. `L₁(x) ≥ 0`, the `s = 0` instance — batch-4 attack 24. Untouched this batch.
4. The residual shallow seat channel `|Im s| > 634`, `0 < Re s − ½ < ½ − c/log(|Im s|+½)`
   — batch-4 attack 26, `rh_iff_shallow_channel_dominates_634`. Untouched this batch.
5. The linear turning point. `kix_zero_pos` gives `A > 4(|x|+1)²`; the true threshold is
   `A > √(x²+¼)`. Attack 16 records the route (Sturm + a far-field non-vanishing input).

**Relocation of the obstruction, stated as a property of these instruments.** After A1–A10
the analytic side of the cell density is fully discharged: every mode's radial factor
`(A²+9)K_{ix}(A) + 6A K′_{ix}(A)` is *proved* positive above one explicit height
(A7 #62), so the sign of every cross term is the sign of its arithmetic phase
`cos(x·log(a/b))`. The `K_{ix}` side is closed; the divisor-phase side is not. This is a
statement about this decomposition, not about the problem.

# EQUIV — carried

- `XiStructure.rh_iff_xiStructure_dominates`; `rh_iff_shallow_channel_dominates_634`.
- The C3 transform / weighted-tail identities from vertical `Ξ` monotonicity to the
  quadratic-ramp leaf (`second_tail_eq_quadratic_ramp`,
  `sinh_pairing_nonneg_of_second_tail`, `sinh_pairing_nonneg_of_compact`).
- `C3B6.Theta.cellDensity_eq_tsum` — the cell density and its complete theta double sum are
  the same object; this is an identity, not a reduction.

# FAILED — refuted, not retried

- Uniform linear-ramp positivity `T(r,x) ≥ 0`: `T(0,60) = −2.4411414711711282366e−36`.
- Fixed-`d` J-kernel fiber positivity: does not control the outer `cos(xd)` integral.
- `(1,1)` Macdonald mode transferring its zero count to the full double sum (batch-4 §22:
  6 predicted crossings, 1 measured at `x = 21.022`).
- `rampKernel(a+b) = max(a+b,0)²` PSD: `C3B5.A4.rampKernel_not_psd`, quadratic form `−4`.
- Multiplicative Hankel / total-positivity factorization of the mode kernel: refuted at the
  **actual** parameter by `C3B6.Theta.exp_hankel_minor_neg`, for every `A₁ > 0`, `ξ ≠ 0`.
- `tmp/att542_out_floor60.txt` remains inadmissible and supports no claim here.

---

# Skeleton (rule 11), after this batch

```
RH
└─ ∀z, Im z>0 : ‖E*z‖ ≤ ‖Ez‖                        EQUIV    rh_iff_xiStructure_dominates
   ├─ |Im s| ≤ 634 (ORDINATE BAND)                  COMPILED xiStructure_dominates_of_low634
   ├─ |Im s| > 634, deep                             COMPILED xiStructure_dominates_interior_rung
   └─ |Im s| > 634, shallow                          OPEN     rh_iff_shallow_channel_dominates_634
      └─ ∂_y|Ξ(x+iy)|² ≥ 0                           EQUIV    batch-3 §1
         └─ ∫_{u>0} g_y(u)·C(u,x) du ≥ 0             EQUIV    g_y(u)=u·sinh(2yu)
            └─ U_x(s) = ∫_s^∞ (u−s)²/2·C du ≥ 0      OPEN     ← THE LEAF
               ├─ ⟸ C ≥ 0 on (s,∞)                   COMPILED UTail_nonneg_of_cellDensity_nonneg
               │  └─ C = 16·Σ_{(n,m)} mode           COMPILED cellDensity_eq_tsum  (interchange proved)
               │     ├─ each mode exactly evaluated  COMPILED modePair_integral
               │     ├─ radial > 0, all modes        COMPILED radial_mode_pos      ← STRONGER-and-constructive
               │     │  ├─ Bessel ODE                COMPILED kix_bessel_ode
               │     │  ├─ ρ ≤ 1 concluded           COMPILED logDeriv_kix_le_one
               │     │  └─ K_ix > 0, A > 4(|x|+1)²   COMPILED kix_zero_pos
               │     ├─ tail majorant summable       COMPILED summable_modeBound / modePair_integral_abs_le
               │     └─ head beats tail              OPEN     ← the only remaining input
               └─ compact window [0, u₁(x)]          OPEN     untouched
```

**Rule-11 guard check.** The `STRONGER`-and-constructive leaf is `radial_mode_pos`: an
object *exhibited* — the Macdonald function `K_{ix}` built from its integral, its ODE
proved, its logarithmic-derivative ceiling concluded, its positivity established — and
discharged by identity rather than by estimate. It is now **compiled**, not open. The
skeleton is therefore a proof plan, not a restatement; it is not yet a proof, because the
head-dominance arithmetic and the compact window are open.

---

# LITERAL NEXT LEAN STATEMENT

```lean
-- tmp/c3b6_A11.lean, after `import c3b6_A10`, in namespace C3B6.Theta.
-- Discharges the sole Prop-valued input of `cellDensity_pos_of_head_dominant`.
-- Every ingredient is already compiled; what remains is the closed-form tail sum.

theorem modeBound_tail_lt_head (x : ℝ) {u : ℝ}
    (hu : max (modeThreshold x) (8 * (|x| + 1) ^ 2) ≤ modeA 0 0 u) :
    (∑' z : ℕ × ℕ, if z = (0, 0) then (0 : ℝ) else modeBound x u z)
      < modeTerm x u (0, 0)
```

Proof plan, all inputs compiled in this batch:

1. `modeTerm x u (0,0) = π²e^{5u}·radial(A₁)` (`modeTerm_head`), and
   `radial(A₁) ≥ (A₁²−6A₁+6)·kix 0 x A₁ ≥ (A₁²−6A₁+6)·e^{−A₁cosh h}·h/4`
   by `C3B5.A2.radial_ge` (with `logDeriv_kix_le_one`) and `kix_zero_lower`, `h = 1/(|x|+1)`.
2. `modeBound x u (n,m) ≤ π²(ab)²e^{5u}·[((ab·A₁)²+9)+6(ab)A₁]·e^{−δ/2}(1+4/δ)·e^{−(ab−1)A₁}`
   with `δ = A₁`, by `kixConst_le` (`2j ≤ A₁` holds since `A₁ ≥ 8` and `j ≤ 2`).
3. `ab ≥ (a+b)/2` (`prod_ge_half_sum`) splits the tail into a product of two one-dimensional
   geometric-polynomial sums, each summed in closed form by
   `summable_pow_exp_shift` plus `tsum_geometric_of_lt_one`.
4. The comparison closes because the head carries `e^{−A₁cosh h}` with `cosh h < 2`
   (`cosh_lt_two_of_le_one`) while every tail term carries `e^{−(ab−1)A₁} ≤ e^{−A₁}`,
   and the gap `e^{(2−cosh h)A₁}` grows without bound in `A₁ = 2πe^{2u}`.

Then, immediately:

```lean
theorem cellDensity_pos (x : ℝ) {u : ℝ}
    (hu : max (modeThreshold x) (8 * (|x| + 1) ^ 2) ≤ modeA 0 0 u) :
    0 < cellDensity x u :=
  cellDensity_pos_of_head_dominant x u (modeBound_tail_lt_head x hu)

theorem UTail_nonneg (x : ℝ) {s : ℝ}
    (hs : ∀ u ∈ Set.Ioi s, max (modeThreshold x) (8 * (|x| + 1) ^ 2) ≤ modeA 0 0 u) :
    0 ≤ UTail x s :=
  UTail_nonneg_of_cellDensity_nonneg fun u hu => (cellDensity_pos x (hs u hu)).le
```

which is `U_x(s) ≥ 0` above an explicit unconditional height, leaving exactly the compact
window `[0, u₁(x)]`, `2πe^{2u₁(x)} = max (modeThreshold x) (8(|x|+1)²)`.

---

# Artifacts

| file | what |
|---|---|
| `tmp/c3b6_A1.lean` / `.log` / `.olean` | `K_{ix}` constructed, Gaussian majorant, decay bound |
| `tmp/c3b6_A2.lean` / `.log` / `.olean` | differentiation under the integral; **the modified-Bessel ODE** |
| `tmp/c3b6_A3.lean` / `.log` / `.olean` | Liouville normal form; `ρ ≤ 1` concluded; obligation A modulo `K > 0` |
| `tmp/c3b6_A4.lean` / `.log` / `.olean` | `K_{ix} > 0` for `A > 4(\|x\|+1)²`; obligation A hypothesis-free |
| `tmp/c3b6_A5.lean` / `.log` / `.olean` | the exact `(n,m)` cross term and its `p`-integral |
| `tmp/c3b6_A6.lean` / `.log` / `.olean` | quantitative bounds; the summable majorant over `ℕ×ℕ` |
| `tmp/c3b6_A7.lean` / `.log` / `.olean` | head positivity; the remainder bound; obligation-C decompositions |
| `tmp/c3b6_A8.lean` / `.log` / `.olean` | the complete theta double sum, pointwise |
| `tmp/c3b6_A9.lean` / `.log` / `.olean` | **the sum/integral interchange** |
| `tmp/c3b6_A10.lean` / `.log` | the cell density, head-dominance criterion, `U_x` bridge |
| `tmp/c3b5_A1..A3.olean` | batch-5 blocks rebuilt as oleans so this batch composes with them |

No `RequestProject/` or `automorph/` file created or modified. No commits.
