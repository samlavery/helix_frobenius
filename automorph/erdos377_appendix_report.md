# Appendix report — `erdos377_partial.tex`

Written for the auditor. Line numbers refer to `automorph/erdos377_partial.tex`
as it stands after the appendices were appended (25 pp., compiles clean, no
undefined references, no overfull-box errors). Main-text statements
(§1–§7, lines 1–430) were **not** edited except for three placeholder
sentences and the addition of `\newtheorem{definition}`; every substantive
objection is recorded here and flagged in-place in Appendix B as
**[A1]**–**[A10]**.

---

## 1. Status per task

| Task | Status | One-line reason |
|---|---|---|
| **A** — Vaughan computation (Appendix A) | **COMPLETE-WITH-DISCREPANCIES** | Identity, dyadic splitting, weight removal, prime powers and both target ranges all proved; but the Type I term provably cannot be delivered in the coefficient-free form printed in Lemma `vaughan`, and the bilinear range lands on `U/2 ≤ M ≤ Q/U`, not `U ≤ M ≤ Q/U`. See D1, D2. The divisor moment `Σ_{m∼M} τ(m)² ≪ M(log M)³` is proved in full from Mertens only. |
| **B** — regime verification (Appendix B) | **COMPLETE-WITH-DISCREPANCIES** | Every `(F,Q,i,k)` regime for `k ≤ K`, `i ≤ J(k)`, `‖h‖_∞ ≤ H` is covered — three cases, no gap. Ten main-text statements need amendment (D1–D12 below); two of them (**[A4]**, **[A7]**) are errors that break the argument as printed, and **[A10]** adds an unlisted analytic input. Trap checks 1 and 2 both resolved, one favourably and one against the main text. |
| **C** — multidimensional Erdős–Turán (Appendix C) | **COMPLETE** | Proved self-contained via product Fejér-type kernels, with two explicit log-power losses (`log H` in the first term, an outer factor `J` on the sum) that the prompt permits and that §B.9 absorbs with an exponential margin. |

Nothing is BLOCKED. The one place where the paper needs an input it does not
claim — PNT with a classical error term — is unconditional, and Appendix B
gives a variant route (§B.6(d)) that minimises the reliance.

---

## 2. Discrepancy list

Format: **[flag]** — location — what is wrong — proposed fix — why.

### D1. **[Remark A.7(i)]** — Lemma `vaughan`, line 301–303
**Wrong.** The Type I term is printed as `|Σ_{m∼M} Σ_l φ(ml)|` (absolute value
outside the `m`-sum).
**Fix.** Replace by `Σ_{m∼M} max_I |Σ_{l∈I} φ(ml)|`.
**Why.** The Type I sums arise as `Σ_{d≤U} μ(d)(…)` and `Σ_m c_m(…)`. The
coefficients `μ(d)`, `c_m` depend on `m` and are not of constant sign, so they
cannot be removed by partial summation — only pulled outside in absolute value,
at the cost of the `log Q` already present. The paper's own §3 item (I),
line 141–143, already writes the Type I family **with** the absolute value
inside, so the main text is internally inconsistent and Lemma `vaughan` is the
side that is wrong. The `max_I` is separately forced by the removal of the
weight `log l` (Appendix A, §A.4) and by the cut-off at `T` in the passage from
`Λ` to primes.

### D2. **[Remark A.7(ii)]** — Lemma `vaughan`, line 304
**Wrong (by a factor 2).** Bilinear range printed as `U ≤ M ≤ Q/U`.
**Fix.** `U/2 ≤ M ≤ Q/U`.
**Why.** In `Σ₃` one has `b > U` and `ab ≤ 2Q` with `a > U`, so `b < 2Q/U`. A
dyadic ladder `(M, 2M]` covering `(U, 2Q/U]` cannot simultaneously have every
base point `≥ U` and reach `2Q/U`; the bottom base point falls in `[U/2, U]`.
Harmless: Lemma `typeII` is applied only for `M ≥ Q^{1/3}/2`, and its proof
needs only `M` above a fixed power of `log Q`.

### D3. **[Remark A.7(iii)]** — §3 item (I), line 143
**Wrong.** The Type I family is constrained to `M ≤ Q^{1/3}`.
**Fix.** `M ≤ U² = Q^{2/3}`, equivalently `L = Q/M ≥ Q^{1/3}`.
**Why.** Vaughan with `U = Q^{1/3}` — the choice that makes the Type II range
land exactly on the `[Q^{1/3}, Q^{1/2}]` of Lemma `typeII` after the symmetry
reduction — produces Type I sums with `M` up to `U² = Q^{2/3}`. `M ≤ Q^{1/3}`
is unattainable with that `U`, and with a smaller `U` the bilinear range opens
below `Q^{1/3}`, where Lemma `typeII` does not apply. Costs nothing: Lemma
`typeIB` needs only `L` long.

### D4. **[A1]** — Proposition `equi`, line 116; §7, line 364; remark line 190
**Wrong/inconsistent.** Three mutually incompatible schedules for `J`:
`J ≤ c log k` (Prop `equi`), `J(n) = ⌈(loglog n)^{1/3}⌉` (§`schedule`),
`J(k) = ⌊c log k⌋` (remark after `rem:noshortcut`). Moreover for `k < J` the
coordinate `{n/p^{k-i+1}}` is undefined (exponent `≤ 0`).
**Fix.** `J(k) := min(J(n), k)` with `J(n) = ⌈(loglog n)^{1/3}⌉`, and delete
the hypothesis `J ≤ c log k`.
**Why.** Nothing in the analysis needs `J ≤ c log k`; what is needed is
`J(k) ≤ k` and `r ≤ r_max`. The terms `k < J` contribute `Σ_{k<J} 2^{-k}/k = O(1)`,
so the change is free. Note the knock-on at line 409 (D11).

### D5. **[A2]** — §7, lines 368–372
**Imprecise, correct when read as amended.** "the amplitude is
`F_i = h n/Q^{k-i+1}`" is written per level `i`, but the phase
`Ψ_h(x) = Σ_i h_i n x^{-j_i}` is a *sum* of monomials.
**Fix.** State that the governing amplitude is that of the highest
non-vanishing level `i₀ = max{i : h_i ≠ 0}`: `F = |h_{i₀}| n Q^{-j}`,
`j = k−i₀+1`.
**Why.** Lemma `dominance` (Appendix B, §B.2) shows the lower levels are
suppressed by `Σ_{i<i₀} G_i/G_{i₀} ≤ 2He^r/Q ≤ 1/(4e)`, so `Ψ^{(r)}` is
two-sidedly `≍ F(j)_r Q^{-r}`. Without this the derivative test has no
two-sided hypothesis to run on. The displayed range `F ∈ [h, hQ^i]` is then
correct; the stated global bound `F ≤ HQ^{J+1}` is true but slack — the sharp
bound is `F ≤ HQ^J` (because `t ≤ Q` on the whole band).

### D6. **[A3]** — Lemma `vdcr`, line 258–260; Lemma `typeI`, line 279–284
**Two problems, the second fatal as printed.**
(a) Lemma `vdcr`'s first term is `N(λN^{r-2})^{1/(2^r−2)}`. This statement is
*true* (it is weaker than the sharp form, since `N ≥ 1`) but too weak to be
used: with `λN^{r-2} = Fj^r/L²` and `F ≤ L^{r−η}` the first term is `≥ L` for
every `r ≥ 3`, so no saving results.
(b) Lemma `typeI`'s "in particular" clause — a saving on
`L^η ≤ F ≤ L^{r−η}` for a **fixed** `r` — is **false for `r ≥ 5`**. For fixed
`r` the derivative test saves only on the window
`κ ∈ [N^{r−4+2^{3−r}+1/2}, N^{r−1/2}]`, whose lower edge is at `F ≍ L^{r−3.5}`,
not `L^η`.
**Fix.** Restate Lemma `vdcr` with first term `Nλ^{1/(2^r−2)}` (Lemma
`vdcrB`, proved in Appendix B §B.1). Restate Lemma `typeI` with `r` chosen
**as a function of `F` and `L`**: `r = max(2, ⌈log F/log L⌉ + 1)`, saving
exponent `η' ≍ 2^{-r}`.
**Why.** The windows for consecutive `r` overlap (width `3.5 − 2^{3−r}`,
overlap `≥ 2.5`), so their union over `2 ≤ r ≤ r_max` is `[N^η, N^{r_max−1/2}]`;
that is how a single family covers all amplitudes. `r = J+3` in §`schedule` is
the *maximum* `r` needed, not a fixed choice. See also D9.

### D7. **[A5]** — Lemma `typeI`, line 288 (proof) and line 278 (statement)
**Wrong constant.** `g^{(r)}(l) ≍_{j,r} F j^r/L^r`, with `j^r` carried through
the display.
**Fix.** The exact factor is the Pochhammer `(j)_r = j(j+1)⋯(j+r−1)`, not `j^r`.
**Why.** `(d/dx)^r x^{-j} = (−1)^r (j)_r x^{-j-r}`. For `j = 1` this is `r!`, not
`1`. The statement is not literally false (its implied constant is declared to
depend on `j, r`), but `j ≤ K = (log n)^{1−ε_n}` and `r ≤ 3J+3` both grow with
`n`, so the dependence must be explicit. Appendix B carries `(j)_r` and bounds
`1 ≤ (j)_r ≤ ϱ^r`, which is what the slack estimate `ς` needs.

### D8. **[A4]** — §3, line 133 ("partition into dyadic blocks `p ∼ Q`")
**Fatal as printed.** On a dyadic block the ratio
`A = sup|Ψ^{(r)}| / inf|Ψ^{(r)}|` equals `2^{j+r}`, and the `r`-th derivative
test carries the factor `A^{2^{2−r}} = exp(4(j+r)2^{−r} log 2)`. With `j ≍ K`
and `r ≤ 3J+3` this is `exp(Ω(K·2^{−3J})) = exp(Ω((log n)^{1−ε_n}
e^{−O((loglog n)^{1/3})}))`, i.e. **larger than any power of `log n`, and larger
than the saving.**
**Fix.** Replace the dyadic block by the *fine block* `(Q, ρQ]` with
`ρ = 1 + 1/ϱ`, `ϱ = k + r_max`. Then `A ≤ 5` absolutely (Lemma `dominance`).
**Why.** `(1+1/ϱ)^{−ϱ} ≥ e^{−1}`, so every `x^{-j_i-r}` with `j_i + r ≤ ϱ`
varies by at most `e` across the block. The band then carries
`≍ 1 + 2ϱ log n/(k(k+1))` blocks; every estimate below is proportional to the
block length, so summing over blocks reproduces the band with no loss
(eq. `blocksum`). The extra `ϱ` in Vaughan's `Q/U` term is absorbed by
`U = Q^{1/3} ≥ exp((log n)^{ε_n}/3) ≫ ϱ`.

### D9. **[A6]** — Lemma `typeII` proof, line 357–358; statement line 337–339;
### hypothesis line 333–334; §7 line 373
Four separate items, all in the Type II layer. **This is trap check 2.**

(a) **Wrong (missing factor `j`).** "the differenced phase in `m` is
`h n m^{-j}(l^{-j} − l'^{-j})`, a monomial in `m` of amplitude `≍ F|l−l'|/L`."
**Fix.** `≍ F·j|l−l'|/L`.
**Why.** By the mean value theorem `l^{-j} − l'^{-j} = jΔ ξ^{-j-1}`, so the
amplitude carries `j`. The main text's chain
`≍ F|l−l'|/L · (Q/(ML))^j ≍ F|l−l'|/L` silently sets `(j)_1 = 1`.

(b) **Wrong (scale).** The identity `≍ F j|l−l'|/L` is a **fine-block**
statement. Over the dyadic `l`-range that Lemma `typeII` allows,
`|l^{-j} − l'^{-j}| ≍ min(l,l')^{-j} min(1, j|Δ|/L)`, and the two sides differ
by a factor up to `2^j ≤ 2^K`. Explicitly, the honest lower bound over a dyadic
block is `G ≥ F(j|Δ|/L)2^{−j−1}`.
**Fix.** Split the `l`-range into `≪ ϱ` fine blocks before Cauchy–Schwarz;
after expanding, the inner `m`-range is automatically `ρ²`-fine.

(c) **Wrong (statement is stronger than its proof).** The conclusion reads
`|B_M| ≪ Q(log Q)³(M^{-1/2} + L^{-η'/2})`. The proof applies Lemma `typeI` **in
the variable `m`**, so the saving is a power of `M`, not `L`; and the diagonal
gives `QL^{-1/2}`, not `QM^{-1/2}`.
**Fix.** `|B_M| ≪ Q(log Q)³(L^{-1/2} + M^{-η'/2})`. (The first summand as
printed is *weaker* than the truth, hence harmless; the second as printed is
*stronger*, hence an error. Both are far below target in the application.)

(d) **Hypothesis too strong to be usable.** "`L^η ≤ F|Δ|/L ≤ L^{r−η}` for
`1 ≤ |Δ| ≤ L`" forces `F ≥ L^{1+η}` (take `|Δ| = 1`). Since `F` ranges down to
`1` in every band, the hypothesis fails on a large part of the range.
**Fix.** Lemma `typeIIB` replaces it by a *count of the exceptional pairs*:
with threshold `G₀ := (Fj)^{4/5}`,
`|B| ≪ Q(log Q)^{5/2}(L^{-1/2} + (Fj)^{-1/10} + M^{−2^{−r_max−2}})`,
valid whenever `Fj ≥ e^{80}ϱ^{10}`. The exponent `4/5` is forced: it is the
unique choice balancing `G₀^{-1/8}` against `(G₀/(Fj))^{1/2}`.

(e) **`r = J+3` (§7, line 373).** **Fix:** `r ≤ 3J+3`.
**Why.** The Type I family runs down to `L = Q^{1/3}`, so
`x = log F/log N ≤ (log H + J log Q)/(⅓ log Q) ≤ 3J+1`. The schedule is
unaffected — `2^{−3J}` and `2^{−J}` are both `exp(−O((loglog n)^{1/3}))` — only
the constant `c` in the first display changes.

### D10. **[A7]** — Proposition `equi`, line 118, versus Lemma `measure`, line 84–91
**Direct contradiction inside the main text.** Proposition `equi` asserts the
density `∏_i |I_i|`; §`density` asserts, of the same top-level coordinate, that
"the top-level condition is **not** uniformly distributed … This is an exact
statement, not a model", and Lemma `measure` gives the hyperbola-weighted
density. Both cannot hold.
**Fix.** Proposition `equi` holds as stated for `t > T₀`; for `t ≤ T₀` the
level-one factor is `σ_ν(I₁) = log((ν+β)/(ν+α)) / log((ν+1)/ν)`, and the
conclusion is `(σ_ν(I₁) ∏_{i≥2} |I_i| + o(1))·#R_ν`.
**Why / cost.** For §`assembly` only an upper bound matters, and
`σ_ν([0,½)) ≤ σ₁ = log(3/2)/log 2 = 0.5850…`, decreasing to `½`. The carry-free
proportion becomes `≤ 1.171·2^{−J(k)}` — an absolute constant, no structural
change. Alternatively §B.6(d): discard the level-one condition entirely (legal,
since only an upper bound is wanted) and use levels `i = 2,…,J(k)+1`; then every
frequency has `i₀ ≥ 2`, hence `F ≥ Q`, and the whole issue evaporates.

### D11. — §`assembly`, lines 407, 409
(a) **Wrong cut-off.** `Σ_{K<k} C/k |_{k ≤ log₃ n}`.
**Fix.** `k ≤ log₂ n = log n/log 2`.
**Why.** `k = ⌊log n/log p⌋` and `p ≥ 2`, so `k` runs to `log n/log 2`. Read as
an iterated logarithm, `log₃ n` omits almost every band; read as a base-3
logarithm it is still the wrong base. With the correct cut-off,
`Σ_{K<k≤log₂ n} 1/k = log(log₂ n / K) + O(1) = ε_n loglog n + O(1)
= (loglog n)^{2/3} + O(1) = o(loglog n)` ✓.
(b) **Overclaim.** "The first sum is `O(1)` by the choice of `J`."
**Fix.** With the §`schedule` value `J(n)` (constant in `k`) the first sum is
`≍ 2^{−J} log K = exp(−c(loglog n)^{1/3})·loglog n = o(loglog n)`, not `O(1)`.
It is `O(1)` only for the *other* schedule `J(k) = ⌊c log k⌋`. Either suffices
for Theorem 1; the text must choose one (see D4).

### D12. — Proposition `equi`, line 118 (typography, but the display is malformed)
`=\Bigl(\prod_i|I_i|+o(1)\Bigr)\,\pi\bigl(n^{1/k}\bigr)-\pi\bigl(n^{1/(k+1)}\bigr)\bigr)`
has an unmatched `\bigr)` and, as typeset, the second `π` is **subtracted from**
rather than multiplied into the bracket.
**Fix.** `\Bigl(\prod_i|I_i|+o(1)\Bigr)\bigl(\pi(n^{1/k})-\pi(n^{1/(k+1)})\bigr)`.
(It compiles either way; the printed formula is simply not the intended one.)

### D13. **[A8]/[A8′]** — §`schedule`, lines 388–390
(a) **Misnamed.** "the Kusmin–Landau range (`F ≤ L^η`: the phase is nearly
stationary…)". Lemma `KL` requires `‖f'‖ ≥ δ > 0`, which is precisely what a
nearly stationary phase does not supply: for `F ≤ L^η` one has
`|g'| ≍ Fj/L ≪ 1`, so `‖g'‖ = |g'|` is small and Lemma `KL` returns a bound
`≫ L` — nothing. Kusmin–Landau enters only as the engine inside Lemma `vdc2`.
**Fix.** Name the band geometry, not Kusmin–Landau.
(b) **Threshold far too generous, and decisively so.** The derivative-test range
is not `F ≥ L^η`; it is `F ≥ T₀ := e^{80} ϱ^{10} (log Q)^{10A+40}`, a fixed
power of `log n`.
**Why it matters.** The mechanism is the `r = 2` branch of Lemma `typeIB`: the
second-derivative test saves `F^{-1/4}`, a power of the *amplitude alone*, which
does not degrade as the interval lengthens. A saving of a fixed power of `log Q`
— all this paper asks for — is therefore already available at `F` a fixed power
of `log Q`. **This is not a cosmetic improvement.** At the printed threshold
`L^η` the direct count of the residual regime would require primes counted in
intervals of relative length `P^{−η/3}`, which is not available unconditionally;
at `T₀` the same count needs only intervals of relative length
`(log n)^{−10A−51}`, which PNT with a classical error term supplies with an
exponential margin. As printed, §`schedule`'s residual regime is not executable;
with the corrected threshold it is.

### D14. **[A9]** — §`schedule`, line 385
`log L ≫ log Q` — a typo, since `L ≤ Q`.
**Fix.** `log L ≍ log Q` (precisely `log L ≥ ⅓ log Q`). The rest of the sentence
is correct and is the inequality that makes the schedule work.

### D15. **[A10]** — §3, the input list, lines 166–171
**Incomplete input list.** "The complete inputs of this paper are … the
Chebyshev–Mertens bounds of §`density` (machine-verified in finite form) …".
**Fix.** Add: the prime number theorem with a classical (de la Vallée Poussin)
error term `π(y) = li(y) + O(y e^{−c√log y})`.
**Why.** Component (B)'s band mass is, from Mertens with its *elementary* error,
`log(1+1/k) + O(k/log n)`; the error exceeds the main term `≍ 1/k` as soon as
`k > √log n`, whereas the schedule runs to `K = (log n)^{1−ε_n} ≫ √log n`.
Shrinking `K` to `√log n` is not an option: the tail would then contribute
`½ loglog n`, not `o(loglog n)`. So PNT-with-classical-error is genuinely
required, for **every** band with `k > √log n`, independently of the residual
regime. This is an internal inconsistency rather than a new hypothesis —
`rem:noshortcut` (line 176–182) already reasons with PNT-with-classical-error,
and that theorem is unconditional — but it is not elementary in the sense the
input list implies, and it is not among the machine-verified components.
**Margin check.** Relative error `≪ k T₀ e^{−c√log P}` with
`log(kT₀) = O(loglog n)` and `√log P ≥ (log n)^{ε_n/2} = exp(½(loglog n)^{2/3})`
— overwhelming.

---

## 3. Constant ledger

Every constant instantiated or adjusted, in order of appearance.

### Appendix A
| Quantity | Value / bound | Where | Note |
|---|---|---|---|
| `\|c_m\|` | `≤ log m ≤ 2 log U ≤ log Q` | §A.3 | uses `Σ_{de=m} Λ(e) = log m` |
| `\|w(m)\|` | `≤ τ(m)`, supported on `m > U` | §A.3 | `w = μ_{>U} * 1` |
| weight-removal factor | `≤ 2 log(2Q)` | eq. `remove-log` | `log(2Q) + log 2`; `∫_{Q/d}^{T/d} du/u ≤ log 2` |
| dyadic ladder lengths | `≤ log₂U+1`, `≤ 2log₂U+1`, `≤ ⌈log₂(Q/U²)⌉+1` | §A.5 | all `≪ log Q` |
| `Σ_{a≥1}(2a+1)x^a` | `= x(3−x)/(1−x)²` | Lemma `tau2` | exact |
| Euler-factor bound | `1 + x(3−x)/(1−x)² ≤ (1−x)^{-3}` for `0<x≤½` | Lemma `tau2` | proved by `(1−x)³ + x(3−x)(1−x) = 1 − x² ≤ 1` — **equality margin `x²`**, i.e. tight only as `x→0` |
| `Σ_{m≤x} τ(m)²` | `≤ x ∏_{p≤x}(1−1/p)^{-3} ≪ x(log x)³` | Lemma `tau2` | implied constant `= e^{3M+o(1)}` from Mertens |
| prime powers | `≪ Q^{1/2} log Q` | §A.6 | `Σ_{2≤i≤log₂2Q} Σ_{p≤(2Q)^{1/i}} log p ≪ Q^{1/2}+Q^{1/3}log Q` |
| `Λ → π` factor | `≤ 2/log Q` | eq. `toprimes` | `∫_Q^{2Q} dT/(T log²T) ≤ log2/log²Q` |
| **bilinear range endpoint** | `U → U/2` | Remark A.7(ii) | **adjusted**, see D2 |

### Appendix B — the `2^{O(r)}` tracking (trap check 1)
| Quantity | Value / bound | Where | Note |
|---|---|---|---|
| `C_r` (r-th derivative test) | `C_r ≤ (2 + 12 C_{r−1})^{1/2}`, fixed point `6+√38 < 13`, so `C_r ≤ max(c₂, 13)` **for every `r`** | Lemma `vdcrB` | **The `2^{O(r)}` growth does not occur.** The induction squares the sum, applies the hypothesis, then takes a square root; the constants therefore *converge* rather than compound. This is the favourable half of trap check 1. |
| `A^{2^{2−r}}` | the *actual* hazard | Remark `trap1` | On a dyadic block `A = 2^{j+r}` and `A^{2^{2−r}} = exp(Ω(K 2^{−3J}))` ≫ any power of `log n`. Forces the fine block. |
| Weyl `H` | `H = ⌈λ^{−2μ_r}⌉ ∈ [λ^{−2μ_r}, 2λ^{−2μ_r}]` | Lemma `vdcrB` | exact by the identity `θ(1−2μ_r) = 2μ_r`, verified symbolically |
| `Σ_{h<H} h^{±θ}` | `≤ 2H^{1±θ}` for `θ ≤ ½` (i.e. `r ≥ 3`) | Lemma `vdcrB` | |
| degenerate ranges | `λ ≥ 1`; `λ^{−2μ_r} ≥ N` (uses `2^{r−1}−1 ≥ 4−2^{3−r}`, equality at `r=3`) | Lemma `vdcrB` | |
| `N ≤ 2` | absorbed by `C₀ ≥ 1` via AM–GM `B_r ≥ 2N^{1−β_r/2} ≥ 2` | Lemma `vdcrB` | |
| **`2^{O(J)}` vs. the saving** | `2^{O(r)} = exp(O((loglog n)^{1/3}))` vs. saving `exp(c (log n)^{ε_n} 2^{−3J−4}) = exp(exp((loglog n)^{2/3}(1+o(1))))` | Remark `trap1`, §B.8 | the **logarithm** of the saving already exceeds `2^{O(J)}`'s logarithm exponentially |

### Appendix B — geometry, dominance, adaptive `r`
| Quantity | Value / bound | Where |
|---|---|---|
| `r_max` | `3J+3` (**not** `J+3`; D9(e)) | eq. `rmax` |
| `ϱ`, `ρ` | `ϱ = k + r_max ≤ 3 log n`, `ρ = 1 + 1/ϱ` | eq. `rmax` |
| block count | `≤ 1 + 2ϱ log n/(k(k+1))` | §B.3 |
| dominance ratio | `Σ_{i<i₀} G_i/G_{i₀} ≤ 2He^r/Q ≤ 1/(4e)`, needs `Q ≥ 8eHe^{r_max}` | Lemma `dominance` |
| `λ`, `A` | `λ = (3/4e)F(j)_r Q^{-r}`, `A ≤ 5e/3 < 5` | Lemma `dominance` |
| `(j_i)_r/(j)_r` | `≤ (j_i/j)^r ≤ e^{r(i₀−i)/j} ≤ e^{r(i₀−i)}` | Lemma `dominance` |
| `log Q` floor | `≥ ½(log n)^{ε_n} = ½exp((loglog n)^{2/3})` | eq. `logQ` |
| slack `ς` | `= r(log ϱ + 8)/log N ≪ (loglog n)^{4/3}/(log n)^{ε_n} = o(1)` | Lemma `typeIB`, §B.7 |
| window (fixed `r`) | `κ ∈ [N^{r−4+2^{3−r}+1/2}, N^{r−1/2}]`, width `3.5−2^{3−r}`, overlap `≥ 2.5` | Remark `window` |
| `η'` | `x/4` at `r=2` (saving `F^{−1/4}`); `1/(2(2^r−2)) ≥ 2^{−r_max−1}` at `r ≥ 3` | Lemma `typeIB` |
| `x` range | `0 < x ≤ 3J+1` | eq. `xrange` |
| **`T₀`** | `e^{80} ϱ^{10} (log Q)^{10A+40} ≤ (log n)^{10A+50}` | eq. `T0` |
| `r=2` admissibility | `ς ≤ x/4 ⟺ F ≥ e^{64} ϱ^8` | §B.7 |
| Type II threshold | `G₀ = (Fj)^{4/5}` — **forced**, balances `G₀^{−1/8}` against `(G₀/(Fj))^{1/2}` | Lemma `typeIIB` |
| Type II hypothesis | `Fj ≥ e^{80} ϱ^{10}`; reaches `≪ Q(log Q)^{−A}` at `Fj ≥ (log Q)^{10A+40}` | Remark `typeIIreach` |
| `U` | `Q^{1/3}`; Type I `M ≤ Q^{2/3}`, bilinear `[Q^{1/3}/2, Q^{1/2}]` after symmetry | §B.7 |
| §`schedule` display 1 | `η' ≥ 2^{−3J−4} ≥ exp(−c(loglog n)^{1/3})`, `c = 4log2` | §B.8 — **verified** |
| §`schedule` display 2 | `L^{η'} ≥ exp(c'(log n)^{ε_n} e^{−c(loglog n)^{1/3}})`, `c' = 1/6` | §B.8 — **verified** |

### Appendix C
| Quantity | Value / bound | Where |
|---|---|---|
| `\|1̂_I(h)\|` | `≤ 1/(1+\|h\|)` for **all** `h`, constant exactly 1 | Lemma `fourier1` (uses `π\|h\| ≥ 1+\|h\|`) |
| kernel | `Φ = φ_θ^{*2s}`, `θ = 2/(πH)`, `s = ⌈log H⌉`, `w = sθ = 2s/(πH)` | Prop. `onesided` |
| truncation tail | `τ ≤ (1/πs)(πθH)^{−2s} = 4^{−s}/(πs) ≤ 1/H` | Prop. `onesided` (uses `πθH = 2`, `4^{−log H} = H^{−1.386}`) |
| mean error | `ε_H = 2w + 1/H ≤ (4 log H + 6)/H` | Prop. `onesided` |
| product inflation | `(1+ε_H)^J ≤ e^{Jε_H} ≤ e` (requires `Jε_H ≤ 1`) | Thm. `ET` |
| final constant | `C = 3e` | Thm. `ET` |

---

## 4. The regime table (verbatim from Appendix B, §B.7)

Fix a band `k ≤ K`, a fine block `Q = (Q, ρQ]`, a level index `i ≤ J(k)`, and a
frequency `h` with `0 < ‖h‖_∞ ≤ H`. Set `U := Q^{1/3}`, so the Type I range is
`M ≤ U² = Q^{2/3}` (i.e. `L = Q/M ≥ Q^{1/3}`) and the bilinear range is
`Q^{1/3}/2 ≤ M ≤ Q^{2/3}`, reduced by Lemma `typeIIsym` to
`Q^{1/3}/2 ≤ M ≤ Q^{1/2}`.

```
 #  | regime                    | amplitude F              | r used                        | covering statement
----+---------------------------+--------------------------+-------------------------------+----------------------------
 1  | i0 >= 2, any t            | Q <= F <= H Q^J          | max(2, ceil(x)+1) <= 3J+3     | Lem. typeIB, typeIIB
 2  | i0  = 1, F >= T0          | T0 <= F <= H Q           | 2 <= r <= 5                   | Lem. typeIB, typeIIB
 3  | i0  = 1, F <  T0          | 1 <= F < (log n)^(10A+50)| ---                           | §B.6(b), or eliminated
    |                           |                          |                               |   by §B.6(d)
----+---------------------------+--------------------------+-------------------------------+----------------------------
      sub-cases of 1-2, by the window of Remark `window`:
----+---------------------------+--------------------------+-------------------------------+----------------------------
 1a | x in (0,1]                | F <= N                   | r = 2                         | eta' = x/4, saving F^(-1/4)
 1b | x in (1,2]                | N < F <= N^2             | r = 3                         | eta' = 1/12
 1c | x in (2,3]                | N^2 < F <= N^3           | r = 4                         | eta' = 1/28
 1d | x in (s-1,s], 4<=s<=3J    | N^(s-1) < F <= N^s       | r = s+1                       | eta' = 1/(2(2^(s+1)-2))
----+---------------------------+--------------------------+-------------------------------+----------------------------
      Type II only: replace F by G ~ F j |l-l'| / L and N by N_m ~ M/rho;
      pairs with G < G0 = (F j)^(4/5) are counted, not estimated (Lem. typeIIB).
```

**Verification that cases 1–3 exhaust and overlap.** Case 1 is `i₀ ≥ 2`; cases 2
and 3 are `i₀ = 1` with `F ≥ T₀` and `F < T₀` respectively. These are disjoint
and exhaustive. Case 2 has `F = |h₁|t ≤ H P₀ ≤ HQ` by eq. `trange`, so
`x ≤ 3(1 + log H/log Q) = 3+o(1)` and `r = max(2, ⌈x⌉+1) ≤ 5` suffices.
Case 1 has `F ≥ Q`, so `x ≥ 1`, and
`F ≤ HQ^J`, so `x ≤ 3J+1`. Sub-cases 1a–1d are the windows of Remark `window`;
by eq. `xrange` they cover every `x > 0` arising in cases 1–2 with `r ≤ 3J+3`,
and the hypothesis `ς ≤ x/4` needed in 1a is supplied by `F ≥ T₀`.
**No regime is uncovered.**

---

## 5. Harder than the main text implies / easier than the main text implies

### Harder

1. **The fine-block refinement (D8) is not a technicality; it is load-bearing.**
   Every implied constant in §3's Type I/II families is `2^{O(j)}` on a dyadic
   block, and `j` runs to `K = (log n)^{1−ε_n}`. Nothing in the paper's
   architecture survives on dyadic blocks. Appendix B rebuilds §3–§6 on the
   scale `1 + 1/(k+r_max)`, which required proving a dominance lemma from
   scratch (Lemma `dominance`) — there is no counterpart in the main text.

2. **The phase is not a monomial.** §3–§6 treat `e(h n/(ml)^j)` as if a single
   `(F, Q, i)` were in play, but the Weyl sum for a frequency vector `h` has a
   `J`-term phase whose derivatives can cancel. Establishing that the top
   non-vanishing level dominates (D5) is a genuine prerequisite for every
   derivative test in the paper, and it is what fixes the meaning of `F`.

3. **Lemma `typeI`'s "in particular" clause is false as stated (D6b).** The
   fixed-`r` window has width `≈ 3.5`, not `[L^η, L^{r−η}]`. Recovering the
   intended statement required the adaptive rule `r = max(2, ⌈log F/log L⌉+1)`
   and a verification that consecutive windows overlap — otherwise there are
   amplitude bands no `r` covers.

4. **Type II needed rebuilding, not checking (D9).** Of the five components of
   Lemma `typeII` — differenced amplitude, scale of validity, saving variable,
   hypothesis, coefficient symmetry — four were wrong or unusable. In
   particular the hypothesis excludes most of the range it is applied to, and
   the fix (an exceptional-pair count with the balanced threshold
   `G₀ = (Fj)^{4/5}`) has no analogue in the main text.

5. **The symmetry reduction `M ≤ Q^{1/2}` is not free.** Vaughan delivers
   `M` up to `Q/U`; Lemma `typeII` covers only `M ≤ Q^{1/2}`. Bridging them
   requires exchanging the roles of `m` and `l`, which the *statement* of
   Lemma `typeII` does not permit (its coefficient hypotheses are asymmetric:
   `|a_m| ≤ τ(m)`, `|b_l| ≤ log l`). Lemma `typeIIsym` proves the exchanged
   form; the point is that the proof uses only `Σ|a|² ≪ M(log 2M)³` and
   `|b|_∞ ≤ log Q`, both of which survive the exchange.

6. **PNT with a classical error term is unavoidable (D15).** Not for the
   residual regime — for the band mass itself, at every `k > √log n`. The
   paper's input list does not contain it.

7. **The multidimensional Erdős–Turán minorant.** The product of one-sided
   minorants is not a minorant unless the factors are non-negative, and
   band-limited non-negative minorants with the right mean are exactly the
   extremal problem the prompt rules out. Appendix C routes around this with a
   telescoping inequality (Lemma `telescope`), at the cost of a factor `J`.

### Easier

1. **The `r`-th derivative test constant is bounded uniformly in `r`** (trap
   check 1). The recursion `C_r = (2 + 12C_{r−1})^{1/2}` has an attracting
   fixed point `< 13`; there is no `2^{O(r)}`. The paper's own worry — and the
   prompt's — is misplaced. (The `A^{2^{2−r}}` factor is where the real
   hazard lives; see D8.)

2. **The choice of Weyl parameter in the `r`-th derivative test is exact, not
   optimised.** `H = λ^{−2/(2^r−2)}` balances all three terms *simultaneously*,
   because `θ(1 − 2μ_r) = 2μ_r` holds identically:
   `(1/(2^{r−1}−2))·((2^r−4)/(2^r−2)) = 2/(2^r−2)`. No optimisation calculus is
   needed, contrary to the parenthetical in the proof of Lemma `vdcr`.

3. **The derivative tests reach far further down in amplitude than the paper
   claims (D13b).** The `r = 2` saving is `F^{−1/4}` — a power of the amplitude
   alone. Since the paper needs only a power of `log Q`, the cancellation range
   extends down to `F ≥ (log n)^{O(1)}`, not `F ≥ L^η`. This is the single most
   consequential finding of the audit: it shrinks the residual regime from
   "requires primes in intervals of relative length `P^{−η/3}`" (unreachable)
   to "requires primes in intervals of relative length `(log n)^{−O(1)}`"
   (routine). Likewise Type II reaches `Fj ≥ (log Q)^{10A+40}`.

4. **The `2^{−J}` factor is robust.** Because §`assembly` needs only an upper
   bound on the carry-free mass, any one level condition may be discarded. This
   makes the entire nearly stationary regime optional (§B.6(d)): re-index to
   levels `2,…,J(k)+1`, and every frequency has `F ≥ Q`. The hyperbola-weighted
   density of §`density` is then corroboration rather than a logical input.

5. **The schedule has an enormous margin.** Both displayed inequalities of
   §`schedule` are true, and not marginally: `log(L^{η'}) ≥
   exp((loglog n)^{2/3}(1+o(1)))` against a requirement of `A loglog n`. The
   correction `r = J+3 → r ≤ 3J+3` changes only a constant, and the Appendix C
   losses (`log H`, and an outer `J`) are invisible at this margin.

6. **`Σ_{m∼M} τ(m)² ≪ M(log M)³` is genuinely elementary.** `τ² = h * 1` with
   `h(p^a) = 2a+1 > 0`, and the Euler factor obeys
   `1 + x(3−x)/(1−x)² ≤ (1−x)^{−3}` by the one-line identity
   `(1−x)³ + x(3−x)(1−x) = 1 − x²`. Only Mertens is needed.

---

## 6. What an auditor should check first

In descending order of consequence:

1. **D13b** (the true threshold `T₀`) — everything about the residual regime's
   feasibility turns on the claim that the `r = 2` saving is `F^{−1/4}`
   independent of `N`. Verify from Lemma `typeIB`'s last display and its proof.
2. **D8 / Remark `trap1`** — the `A^{2^{2−r}} = exp(Ω(K 2^{−3J}))` computation.
   If this is wrong, the fine-block refinement is unnecessary; if it is right,
   §3's dyadic partition is fatal as printed.
3. **D15** — whether PNT-with-classical-error is truly required. The pivot is
   `Mertens error O(k/log n)` vs. `main term ≍ 1/k` at `k = √log n`.
4. **D10** — the contradiction between Proposition `equi` and Lemma `measure`.
   Both are main-text statements; one of them must change.
5. **Lemma `vdcrB`'s constant recursion** `C_r = (2+12C_{r−1})^{1/2}` — the
   claim that the constant is uniform in `r`.
6. **Lemma `typeIIB`'s exceptional-pair count** and the forced exponent `4/5`.
7. **Appendix C's two losses** — confirm they are the only ones, and that
   Lemma `fourier1`'s constant is exactly 1 (it is what keeps the weight
   `∏(1+|h_ν|)^{−1}` free of a `C^J`).
