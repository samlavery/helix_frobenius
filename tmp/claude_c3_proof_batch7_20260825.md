# C3 proof batch 7 — 2026-08-25

Working dir `/Users/samuellavery/work/helix_frobenius`. New Lean under `tmp/c3b7_*`.
No `RequestProject/`, `automorph/` or other tracked file edited. No commits.

**Compilation status.** My `lake env lean` invocations are permission-gated in this session.
Every Lean file below is written and patched but **NOT declared compiled by me**; OpenAI runs
the compiler and feeds errors back. B1 has been through one adjudicator round (three errors,
all patched — see §5). B2/B3 are first submission.

---

## 0. CORRECTIONS TO THE BATCH-6 LEDGER

### 0.1 "No Python" — WRONG AS WRITTEN
Batch 6 says *"No Python, no numerics, no quadrature."* Clauses 2–3 true; clause 1 false.
Python was used in batch 6 **only as a mechanical text editor on `.lean` files**
(`python3 - <<'PYEOF'` heredocs doing literal `str.replace` to apply compiler-guided fixes:
`pow_le_pow_left → pow_le_pow_left₀`, `abs_add → abs_add_le`, inserting `ring`, replacing
proof blocks). No Python produced any number entering any claim. Correct wording:
**"No numerical experiments; no quadrature; no numeric evidence. Python used only as a text
editor of Lean source."** This also means batch 6 did not comply with the letter of
CLAUDE.md ground rule 2. Process defect, not mathematical: every batch-6 claim rests on
`lake env lean` output alone.

### 0.2 A4's radial theorem carries TWO thresholds
```lean
theorem C3B6.Bessel.radial_kix_pos_at {x A : ℝ} (h8 : 8 ≤ A) (hx : 4*(|x|+1)^2 < A) : …
theorem C3B6.Bessel.radial_kix_pos_uncond {x a : ℝ} (ha8 : 8 ≤ a) (hax : 4*(|x|+1)^2 < a) : …
```
At `x = 0` the quadratic reads `4 < A`, which does **not** give `8 ≤ A`. The `8` comes from
`C3B5.A2.radial_pos_of_ge_eight` (makes `A²−6A+6 > 0`); the quadratic from `kix_zero_pos`.
Both load-bearing on `A ∈ (4(|x|+1)², 8)`.

### 0.3 `UTail` is a raw Bochner integral
`C3B6.Theta.UTail x s = ∫ u in Ioi s, (u−s)²/2 * cellDensity x u`. Mathlib's Bochner integral
is `0` on non-integrable integrands, so `UTail_nonneg_of_cellDensity_nonneg` is *vacuously*
available when integrability fails; batch 6's docstring sold this as a feature ("No
integrability hypothesis is needed"), which is backwards. The real interface is
`RequestProject/WeightedTailPrimitive.weighted_tail_primitive_identity`, whose `hprod` is
supplied by `WeightedTailSinhBridge.triF_prod_integrable` from
`IntegrableOn (fun u => g u * |W u|) (Ioi 0)`.
**Batch-7 response:** `C3B7.UTail_eq_zero_of_not_integrable` records the defect as a theorem;
`C3B7.cellDensity_abs_le` supplies the decay bound a genuine integrability proof consumes.
Full integrability remains **OPEN** (§ OPEN 2).

---

## 1. Chart dictionary (preserved verbatim)
Native helix `Re s > 0`, phasors enter at `Re s = 0`. Xi chart `z = i(s−1/2)`:
`Re z = −Im s` (ordinate), `Im z = Re s − 1/2` (depth). `E`/`E*` = conjugate double
helix/anti-helix; chart conjugation is the FE reflection `s ↦ 1 − conj s`. Carrier chart:
physical height `Z`, analytic ordinate `t = log Z`. Native harmonization `π/3`:
`N_{π/3}(e^t)`; unit-1 **scalar receiver** `R_1(e^t) = 1 + θ(t)/π`.
`S(t) = N_{π/3}(e^t) − R_1(e^t)`, **distinct** from Xi-chart `z` and from the Hermitian
pencil `S_t`. Distinct-event / multiplicity / classical-strip ledgers stay typed separately:
`S_class = S_mult + N_off^mult`, `S_mult = S_ev + excess multiplicity`.

---

## 2. FAILED — the primary candidate is refuted

```lean
theorem modeBound_tail_lt_head (x : ℝ) {u : ℝ}
    (hu : max (modeThreshold x) (8 * (|x| + 1) ^ 2) ≤ modeA 0 0 u) :
    (∑' z : ℕ × ℕ, if z = (0,0) then 0 else modeBound x u z) < modeTerm x u (0,0)
```
**FALSE.** Not formalized, per instruction.

Unfolded to plain math (both sides divided by the common positive `π²e^{5u}`), with
`A₁ = modeA 0 0 u = 2πe^{2u}`, `a=n+1`, `b=m+1`, `k=ab`, `A_z = kA₁`,
`C_j = kixConst j A₁ = ∫_0^∞ e^{−A₁/2}e^{(j−A₁/2)w−(A₁/4)w²}dw`, `d(k)` = divisor count:
```
tail = Σ_{k≥2} d(k)·k²·[ (A_z²+9)C₀ + 6A_z C₁ ]·e^{−(A_z−A₁)}
head = (A₁²+9)K_{ix}(A₁) + 6A₁K′_{ix}(A₁)
thresh(x) = max( max(8, 4(|x|+1)²+1), 8(|x|+1)² )
```

### Hostile numerical table (`tmp/c3b7_falsify.py` → `tmp/c3b7_falsify_out.txt`)
mpmath `dps = 40`; `k`-sum truncated at `K = 60`; **certified remainder**
`rem ≤ (K+1)^5 · e^{−K A₁} · 1.05 · M`, `M = (A₁²+9)C₀+6A₁C₁`, using
`term_k ≤ d(k)k²·k²M e^{−(k−1)A₁} ≤ k⁵M r^{k−1}`, `r = e^{−A₁} ≤ e^{−8}`, and
`Σ_{j≥0}(1+j)^5 r^j ≤ 1.05`. At `A₁ ≥ 8`, `r^60 ≤ e^{−480}`, so truncation is ≥ 200 orders
below every printed digit. Verdicts are declared `HOLDS` only when `tail + rem < head`.

**COUNTEREXAMPLES (6):**

| x | A₁ | position | head | tail | tail/head |
|---|---|---|---|---|---|
| 0 | 8.0 | **AT threshold** | 3.23463931463e−3 | 3.96728421314e−3 | **1.22649971983** |
| 0 | 8.0008 | just above | 3.23306532552e−3 | 3.96280641701e−3 | 1.22571183011 |
| 1e−6 | 8.00001600001 | AT threshold | 3.23460782948e−3 | 3.96719460772e−3 | 1.22648395628 |
| 1e−6 | 8.00081600161 | just above | 3.23303384814e−3 | 3.96271690354e−3 | 1.22569607671 |
| 0.01 | 8.1608 | AT threshold | 2.92926292723e−3 | 3.16143932271e−3 | 1.07926102957 |
| 0.01 | 8.16161608 | just above | 2.92776972210e−3 | 3.15779739581e−3 | 1.07856754306 |

Crossover scan at `x = 0`: `A₁=8` → 1.2265 **FAILS**; `8.5` → 0.8304; `9` → 0.5732;
`10` → 0.2848; `12` → 0.0783; `16` → 0.00734. Crossover ≈ `A₁ ≈ 8.3`.
Holds at every tested `x ≥ 0.05` and at every `A₁ ≥ 1.25×`threshold.

### Validation (bounded-domain only; no unbounded quadrature)
* `besselk(ix, A)` real to `|Im| ≤ 2.5e−104`; Bessel recurrence
  `K_{ν−1} − K_{ν+1} = −2νK_ν/A` at `ν = ix` to rel-err `≤ 4.02e−47` across
  `(x,A) ∈ {(0,8),(0,16),(1,10),(10,40),(21.022,100),(60,300)}`.
* `kixConst` closed form (`erfc`) vs quadrature on `[0,20]`: rel-err `≤ 1.09e−40`, with
  analytic tail beyond `W=20` bounded by `e^{−A/2}e^{jW−(A/4)W²}(4/A) ≤ 1.6e−341`.

### Cause, in plain math
`kixConst j δ` bounds the **majorant** `coshMaj`, which carries rate `e^{−δ/2}`, not
`K_{ix}`'s true rate `e^{−δ}` — `C3B6.Bessel.coshMaj` was built from
`cosh w ≥ (1+w+w²/2)/2`, and the `/2` costs a factor `e^{A/2}`. At `A₁ = 8`:
`kixConst 0 8 = 3.858823e−3` versus `K_0(8) = 1.464707e−4` — factor **26.3** of pure slack.
The `(0,1)+(1,0)` modes alone then exceed the head.

---

## 3. Batch-7 replacement — written, patched, NOT yet declared compiled

### `tmp/c3b7_B1.lean` — mode-specific majorant (attack family 1)
| theorem | statement |
|---|---|
| `self_le_sinh` | `0 ≤ t → t ≤ Real.sinh t` |
| `cosh_eq_one_add_two_sinh_half_sq` | `Real.cosh w = 1 + 2 * Real.sinh (w/2)^2` |
| `one_add_sq_half_le_cosh` | `1 + w^2/2 ≤ Real.cosh w` (all real `w`) |
| `lin_le_quad` | `0 < A → j*w ≤ j^2/A + A/4*w^2` |
| **`coshMoment_sharp_le`** | `0 < A → coshMoment j A ≤ exp(−A)·exp(j²/A)·(1+4/A)` |
| `kix_abs_le_coshMoment` | `0 < A → \|kix j x A\| ≤ coshMoment j A` |
| `exp_inv_le` | `2 ≤ A → exp(1/A) ≤ 1 + 2/A` |
| **`radial_abs_le_sharp`** | `8 ≤ A → \|C3B5.A2.radial A (kix 0 x A) (kix 1 x A)\| ≤ 2(A+3)²·exp(−A)` |

Rate is `e^{−A}`, the true rate of `K_{ix}`. `(A²+9) + 6A = (A+3)²` exactly.

### `tmp/c3b7_B2.lean` — sharp majorant + hyperbola-factorised tail (families 1, 2, 5)
```lean
def modeBndS (x u : ℝ) (z : ℕ × ℕ) : ℝ :=
  Real.pi^2 * Real.exp (5*u) * (((z.1:ℝ)+1) * ((z.2:ℝ)+1))^2
    * (2 * (modeA z.1 z.2 u + 3)^2 * Real.exp (-modeA z.1 z.2 u))
def qFac (A₁ : ℝ) : ℝ := Real.exp (-(A₁ - 2))
def gq (A₁ : ℝ) (n : ℕ) : ℝ := qFac A₁ ^ (n + 1)
def tailConst (u A₁ : ℝ) : ℝ :=
  Real.pi^2 * Real.exp (5*u) * (32*(A₁+3)^2*Real.exp (-(2*A₁))) * Real.exp (3*(A₁-2))
```
| theorem | statement |
|---|---|
| `modeTerm_abs_le_sharp` | `8 ≤ modeA 0 0 u → \|modeTerm x u z\| ≤ modeBndS x u z` |
| `qFac_le_quarter` | `20 ≤ A₁ → qFac A₁ ≤ 1/4` (from `e^{18} ≥ 19 ≥ 4`) |
| `summable_gq`, `tsum_gq` | `Σ' gq = q(1−q)⁻¹` |
| `one_add_pow_four_le` | `0 ≤ y → (1+y)^4 ≤ exp(4y)` |
| **`pow_four_exp_le`** | `2 ≤ t → 2 ≤ A → t⁴e^{−tA} ≤ 16e^{−2A}e^{−(t−2)(A−2)}` |
| **`prod_sub_two_ge`** | `1 ≤ a → 1 ≤ b → a+b−3 ≤ ab−2` (the hyperbola step) |
| `modeBndS_le_prod` | off-head: `modeBndS ≤ tailConst·(gq n · gq m)` |
| `tsum_gq_sq_sub` | `20 ≤ A₁ → S² − q² ≤ 4q³` |
| `exp_shift_qcube` | `exp(3(A₁−2))·q³ = 1` (exact cancellation) |
| **`modeBndS_tail_le`** | `20 ≤ A₁ → Σ_{z≠(0,0)} modeBndS ≤ π²e^{5u}·128(A₁+3)²e^{−2A₁}` |

### `tmp/c3b7_B3.lean` — head bound, corrected domination, `UTail` correction (families 5, 6)
| theorem | statement |
|---|---|
| `exp_neg_one_lt` | `exp(−1) < 0.37` |
| `cosh_one_le` | `Real.cosh 1 ≤ 1.55` |
| `cosh_le_of_le_one` | `0 ≤ h → h ≤ 1 → cosh h ≤ 1.55` |
| `exp_three_ge`, `exp_nine_ge` | `13 ≤ exp 3`, `2197 ≤ exp 9` |
| `exp_lower_ge` | `20 ≤ A → 2197(9A/20 − 8) ≤ exp(9A/20)` |
| `radial_ge_kix` | `8 ≤ A → 4(\|x\|+1)² < A → (A²−6A+6)·kix 0 x A ≤ radial A …` |
| **`head_radial_lower`** | `8 ≤ A → 8(\|x\|+1)² ≤ A → (A²−6A+6)·(e^{−A cosh h}·h/4) ≤ radial A …`, `h = 1/(\|x\|+1)` |
| **`tail_lt_head_scalar`** | `20 ≤ A → 0 < h ≤ 1 → 20/A ≤ h → 128(A+3)²e^{−2A} < (A²−6A+6)(e^{−A cosh h}h/4)` |
| `exp_two_le_sixteen`, `modeBndS_le_prod_all`, `summable_modeBndS` | summability of the sharp majorant |
| **`modeBndS_tail_lt_head`** | `20(\|x\|+1)² ≤ modeA 0 0 u → Σ_{z≠(0,0)} modeBndS x u z < modeTerm x u (0,0)` |
| **`cellDensity_pos_uncond`** | `20(\|x\|+1)² ≤ modeA 0 0 u → 0 < cellDensity x u` |
| `UTail_eq_zero_of_not_integrable` | `¬IntegrableOn … → UTail x s = 0` (ledger §0.3, as a theorem) |
| `cellDensity_abs_le` | `\|cellDensity x u\| ≤ 16(modeBndS(0,0) + π²e^{5u}·128(A₁+3)²e^{−2A₁})` |

### Numerical verification of the *provable chain* (`tmp/c3b7_repair_check.py` → `tmp/c3b7_repair_out.txt`)
Every intermediate constant checked, plus the final comparison. **Candidates only.**

| step | check | verdict |
|---|---|---|
| `Σ_{a≥2}a⁴e^{−aA₁} ≤ 32e^{−2A₁}` | A₁ ∈ {16,20,24,32,64} | OK (margin ≈ 2×) |
| `S² − e^{−2A₁} ≤ 65e^{−3A₁}` | same | OK (margin ≈ 2×) |
| `130(A₁+3)²e^{−2A₁} ≥` true sharp tail | A₁ ∈ {16,20,24,32} | OK, ratio 2.22–2.39 |
| final, `A₁ = 16(\|x\|+1)²` | 18 hostile `x` | holds, **worst 0.7558 at x=0** |
| final, `A₁ = 20(\|x\|+1)²` | 18 hostile `x` | holds, **worst 0.1034 at x=0** |
| dense `h`-scan, `A₁ = T/h²`, 200 pts | T=16 → 0.7558 at h=1; T=20 → 0.1034 at h=1 | worst case is `h=1`, i.e. `x=0` |
| `headLow ≤ head` sanity | x ∈ {0,0.1,1,10,60} | OK |

Threshold `20(|x|+1)²` chosen over `16(|x|+1)²`: the latter's 0.756 leaves no room for the
further roundings the Lean proof makes (`2(A+3)²` for the radial bound, `128` for the tail
constant, `cosh h ≤ 1.55`, `e^9 ≥ 2197`, `h ≥ 20/A`).

---

## 4. ATTACK LEDGER — 25 concrete attacks

| # | attack | family | outcome |
|---|---|---|---|
| 1 | Candidate at `x=0`, `A₁=8` (at threshold) | — | **COUNTEREXAMPLE**, ratio 1.2265 |
| 2 | `x=1e−6`, at threshold and just above | — | **COUNTEREXAMPLE**, 1.2265 / 1.2257 |
| 3 | `x=0.01`, at threshold and just above | — | **COUNTEREXAMPLE**, 1.0793 / 1.0786 |
| 4 | `x ∈ {0.05,0.1,0.13,0.2,0.5,1,10,21.022,60,88,200}`, 5 heights each | — | no counterexample |
| 5 | Crossover scan `x=0`, `A₁ ∈ [8,16]` | — | crossover ≈ 8.3 |
| 6 | Diagnose cause: `kixConst 0 8 / K_0(8) = 26.3` | — | slack localized to `coshMaj`'s `e^{−δ/2}` |
| 7 | Mode-specific majorant `coshMoment j A ≤ e^{−A}e^{j²/A}(1+4/A)` | 1 | constructed (B1) |
| 8 | `1 + w²/2 ≤ cosh w` via `cosh = 1+2sinh²(w/2)` | 1 | constructed (B1) |
| 9 | AM–GM `jw ≤ j²/A + Aw²/4` | 1 | constructed (B1) |
| 10 | `e^{1/A} ≤ 1/(1−1/A) ≤ 1+2/A` | 1 | constructed (B1) |
| 11 | Packaging `(A²+9)+6A = (A+3)²` → `\|radial\| ≤ 2(A+3)²e^{−A}` | 1 | constructed (B1) |
| 12 | Hyperbola `ab − 2 ≥ a+b−3` → product factorization | 2 | constructed (B2) |
| 13 | `t⁴e^{−tA} ≤ 16e^{−2A}e^{−(t−2)(A−2)}` from `1+y ≤ e^y` | 2 | constructed (B2) |
| 14 | Geometric collapse `Σ_{z≠(0,0)} q^a q^b = S² − q²` | 2,5 | constructed (B2) |
| 15 | Bracket `S² − q² ≤ 4q³` at `q ≤ 1/4` | 5 | constructed (B2) |
| 16 | Exact cancellation `e^{3(A₁−2)}q³ = 1` | 5 | constructed (B2) |
| 17 | **ALT tail route**: `t^k ≤ k!e^t` geometric bound | 2,10 | **FAILED** — converts `e^{−2A₁}` into `A₁^{−4}e^{−A₁}`; at `A₁=16` overshoots the true tail by ≈3900× and exceeds `headLow`. Rejected in favour of #13 |
| 18 | `cosh 1 ≤ 1.55` from the two `exp 1` decimals | 5 | constructed (B3) |
| 19 | `e^9 ≥ 13³ = 2197` from `Real.sum_le_exp_of_nonneg` | 5 | constructed (B3) |
| 20 | Threshold search `16(\|x\|+1)²` | 5 | rejected — worst ratio 0.756, no room for Lean roundings |
| 21 | Threshold `20(\|x\|+1)²` + dense 200-pt `h`-scan | 5 | adopted — worst 0.1034, worst case `h=1` (`x=0`) |
| 22 | Head lower bound: `radial_ge ∘ logDeriv_kix_le_one ∘ kix_zero_lower` | 5 | constructed (B3) |
| 23 | Final cubic, all-positive coefficients in `A = 20+t` (const 33 745 400, t 31 935 550, t² 3 412 150, t³ 96 305) | 5 | constructed (B3) |
| 24 | `UTail` vacuity documented as a theorem | 6 | constructed (B3) |
| 25 | `cellDensity_abs_le` — the decay bound for the integrability branch | 6 | constructed (B3) |

**Families NOT newly attacked this batch, stated plainly:**
* **(3) conjugate `(n,m)/(m,n)` pairing** — standing instrument
  `C3B6.Theta.modePair_integral_symm` (batch 6, compiled); not extended here. The cancellation
  is already *used* implicitly (the phase is even, so no sine part exists), but no new theorem.
* **(4) Abel / summation-by-parts in `log(a/b)`** — not attempted.
* **(7) theta/Φ representation before mode expansion** — used only as the *evaluator* in the
  falsification (head via `K_{ix}`); no new theorem.
* **(8) operator / positive-kernel / Sturm–Liouville** — not attempted; batch 6's
  `C3B6.Bessel.zDD_eq` (Liouville normal form) is the standing instrument.
* **(9) `S(t)` carrier registration at `π/3`** — not attempted; charts preserved in §1 only.
* **(10) two decompositions per stuck step** — satisfied at two steps (majorant: common-`δ`
  vs mode-specific; tail: `t^k ≤ k!e^t` vs hyperbola factorization, #17 vs #13), not at all.

---

## 5. Adjudicator patch log (B1, run 1)
`env LEAN_PATH=tmp lake env lean tmp/c3b7_B1.lean` → exit 1, three failures, all patched:
1. **line 68** — `Real.cosh_two_mul` in this Mathlib is `cosh (2z) = cosh z ^2 + sinh z ^2`,
   not `2 cosh z ^2 − 1`. Split out as `cosh_eq_one_add_two_sinh_half_sq`, deriving
   `cosh w = 1 + 2 sinh(w/2)²` from that form plus `Real.cosh_sq_sub_sinh_sq` by `linarith`.
2. **line 171** — the extra `rw [div_le_iff₀ …]` after `field_simp` was invalid; the goal
   there is already `A^2 ≤ (A+2)*(A−1)`. Now closed by `nlinarith [hA]`.
3. **line 211** — `div_add'` rewrite pattern absent. Denominators now cleared by an explicit
   `heq : … = (A^3+10A^2+45A+84)/A` (`field_simp; ring`) then `div_le_iff₀ hA0`.

---

## 6. COMPILED (carried from batch 6, unchanged, standard axioms)
`kix_bessel_ode`, `logDeriv_kix_le_one`, `radial_kix_pos_uncond`, `kix_zero_pos`,
`modePair_eq`, `modePair_integral`, `kernel_product_tsum`, `C_tsum`, `cellDensity_eq_tsum`,
`summable_modeBound`, `modePair_integral_abs_le`, `headMode_integral_pos`,
`modePair_integral_symm`, `exp_hankel_minor_neg`, `kixConst_le`, `exp_quarter_sq_integral_le`,
`kix_zero_lower`, `radial_abs_le`, `tsum_pos_of_head_dominant'`. 106 axiom prints, all
`[propext, Classical.choice, Quot.sound]`, 0 escape hatches.

## 7. OPEN
1. **Compilation of B1–B3** — pending adjudicator. Until then §3 is a *candidate*, not a result.
2. **`IntegrableOn (fun u => (u−s)²/2 * cellDensity x u) (Ioi s)`** — required before `UTail`
   may be quoted as the analytic `U_x(s)` (§0.3). `cellDensity_abs_le` gives the
   super-exponential decay `e^{−2πe^{2u}}`; what is missing is measurability + the comparison
   integral. **This is the literal next Lean statement** (§9).
3. **The compact window** `[0, u₁(x)]`, `2πe^{2u₁} = 20(|x|+1)²` — untouched. `cellDensity`
   sign below the threshold is not addressed by any batch-7 result.
4. **`L₁(x) ≥ 0`**, the `s = 0` instance — batch-4 attack 24, untouched.
5. **Residual shallow seat channel** `|Im s| > 634`, `0 < Re s − ½ < ½ − c/log(|Im s|+½)` —
   batch-4 attack 26, untouched.
6. Attack families 3, 4, 7, 8, 9 — not attacked this batch (§4).

## 8. EQUIV (navigation only)
`XiStructure.rh_iff_xiStructure_dominates`; `rh_iff_shallow_channel_dominates_634`;
`C3B6.Theta.cellDensity_eq_tsum` (identity, not a reduction);
`XiStructure.rh_of_xiStructure_isHB` (Hermite–Biehler connector, `A = ξ`).

## 9. LITERAL NEXT LEAN STATEMENT
```lean
-- tmp/c3b7_B4.lean, after `import c3b7_B3`, namespace C3B7.
-- Discharges OPEN 2: makes `UTail` the analytic `U_x(s)` rather than a possibly-vacuous 0.
theorem cellDensity_ramp_integrableOn (x : ℝ) {s : ℝ}
    (hs : ∀ u ∈ Set.Ioi s, 20 * (|x| + 1) ^ 2 ≤ modeA 0 0 u) :
    MeasureTheory.IntegrableOn
      (fun u => (u - s) ^ 2 / 2 * cellDensity x u) (Set.Ioi s)
```
Ingredients already present: `cellDensity_abs_le` (super-exponential majorant
`16(modeBndS(0,0) + π²e^{5u}·128(A₁+3)²e^{−2A₁})` with `A₁ = 2πe^{2u}`), `modeA_head`
(`A₁ = 2πe^{2u}`), and `C3B6.Theta.exp_quarter_sq_integral_le` for the comparison.
Missing: measurability of `cellDensity x ·` in `u` (parametric-integral measurability) and
the integrability of `u ↦ (u−s)²e^{5u}e^{−2πe^{2u}}` on `Ioi s`.

---

## 10. Artifacts
| file | what |
|---|---|
| `tmp/c3b7_falsify.py` / `_out.txt` | hostile falsification, certified truncation — **6 counterexamples** |
| `tmp/c3b7_repair_check.py` / `tmp/c3b7_repair_out.txt` | provable-chain verification, threshold selection, dense `h`-scan |
| `tmp/c3b7_B1.lean` | mode-specific majorant (patched, round 1) |
| `tmp/c3b7_B2.lean` | sharp majorant + hyperbola tail |
| `tmp/c3b7_B3.lean` | head bound, corrected domination, `UTail` correction |

`att542`, `att544`, `att545` not run and not used as evidence. No commits; `HEAD` unchanged.
