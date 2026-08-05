# Pass-3 report — `erdos377_partial.tex` (delta only)

Applied exactly the two adjudicated resolutions plus the `[M3]` knock-on.
`[M4]` and `[M5]` untouched. Lean file untouched. Line numbers are post-edit
(2154 lines).

---

## 1. `[B1]` — amplitude range and `r_max` (recommended route adopted)

| Location | Before → After |
|---|---|
| 213 (§equi) | `Q ≤ F ≤ HQ^J` → `Q ≤ F ≤ HQ^{J+1}` |
| 245 (§equi) | amplitude "varies from `≍ Q` to `HQ^J`" → `HQ^{J+1}` |
| 248 (§equi) | `r ≤ r_max = 3J+3` → `3J+5` |
| 383 (Lemma `typeI`) | `r ≤ r_max = 3J+3` → `3J+5` |
| 385 (Lemma `typeI`) | union covers `T₀ ≤ F ≤ HQ^J` → `HQ^{J+1}` |
| 474 (§schedule) | `F ≤ H Q^J` → `F ≤ H Q^{J+1}` |
| 476 (§schedule) | `r_max = 3J+3` → `3J+5` |
| 955 (`eq:rmax`) | `r_max := 3J+3, ϱ := k+r_max` → `r_max := 3J+5, ϱ := k+r_max = k+3J+5` |
| 975 (`eq:Frange`) | `1 ≤ F ≤ H Q^J` → `1 ≤ F ≤ H Q^{J+1}` |
| 1099 (Rem. `trap1`) | `r ≤ r_max = 3J+3` → `3J+5` |
| 1108 (Rem. `trap1`) | `r ≤ r_max = 3J+3` → `3J+5` |
| 1111 (Rem. `trap1`) | saving `exp(c(log n)^{ε_n} 2^{−3J−4})` → `2^{−3J−6}` |
| 1652–1654 (`eq:xrange`) | numerator `log H + J log Q` → `log H + (J+1) log Q`; `x ≤ 3J+1` → `3J+4`; `r ≤ 3J+3 = r_max` → `3J+5 = r_max` |
| 1680 (table row 1) | `Q ≤ F ≤ HQ^J` → `HQ^{J+1}`; `max(2,⌈x⌉+1) ≤ 3J+3` → `3J+5` |
| 1692 (table row 1d) | `4 ≤ s ≤ 3J` → `4 ≤ s ≤ 3J+4` (forced: `r = s+1 ≤ r_max`) |
| 1710–1711 (§B.7 verification) | `F ≤ HQ^J`, `x ≤ 3J+1`, `r ≤ 3J+3` → `HQ^{J+1}`, `x ≤ 3J+4`, `r ≤ 3J+5` |
| 1731–1742 (§B.8 first display) | `r = r_max = 3J+3` → `3J+5`; `2^{−r_max−1} = exp(−(3J+4)log2)` → `exp(−(3J+6)log2)`; `c := 4log2` → `c := 5log2`; validity line replaced by the accompanying inequality `(3J+6)log2 ≤ c(loglog n)^{1/3}`, i.e. `3J+6 ≤ 5(loglog n)^{1/3}`, justified from `J ≤ (loglog n)^{1/3}+1`; `2^{−3J−4}` → `2^{−3J−6}` |
| 1744–1746 (§B.8, `[A6]`) | "correct bound is `r ≤ 3J+3`" → `3J+5`; `log F/log Q ≤ J+o(1)` → `≤ J+1+o(1)` |
| 1865 (flag `[A6]`) | `r = J+3 → r ≤ 3J+3` → `r ≤ 3J+5` |

**Forced by `eq:Frange`, not on the list — reported:** lines 959–964, `eq:phase`
and the frequency vector: `h ∈ Z^{J(k)}`, `Σ_{i ≤ J(k)}` → `h ∈ Z^{J(k)+1}`,
`Σ_{i ≤ J(k)+1}`. Without it `eq:Frange`'s new bound `F ≤ HQ^{J+1}` has no
support: `F = |h_{i₀}| t Q^{i₀−1} ≤ HQ^{i₀}`, so `F ≤ HQ^{J+1}` requires
`i₀ ≤ J+1`, i.e. the index set must reach `J(k)+1`. ETK dimension is unaffected
(the main line still uses the `J(k)` coordinates `i = 2,…,J(k)+1`).

## 2. `[M3]` knock-on

| Location | Before → After |
|---|---|
| 937–939 (`eq:Jk`) | `J(k) := min{J, k}` → `min{J, k−1}` |
| 940–942 | "so that `j_i ≥ 1` for every `i ≤ J(k)`" → "for every `i ≤ J(k)+1` — the level set `i = 2,…,J(k)+1` being the operative one, by Remark `rem:bridge`" |
| 887–892 (bridge remark) | sentence added: `eq:Jk` sets `J(k) = min{J,k−1}`, which is what makes `j_i ≥ 1` hold on that level set, and `eq:Frange`/`eq:rmax` are stated for `i₀ ≤ J+1`: `F ≤ HQ^{J+1}`, `r_max = 3J+5` |
| 908–912 (bridge remark, flag status) | "Two items … are **not** discharged; each is a one-line change" → "Two further items … are recorded as `[B1]`/`[B2]` at the end of §B.9 and are likewise **resolved in the text**" |
| 1858 (flag `[A1]`) | `J(k) = min(J,k)` → `min(J,k−1)` |

## 3. `[B2]` — target measured against `log n`

| Location | Before → After |
|---|---|
| 190–202 (`eq:weyl`) | `≪ π(P)/(log P)^A` → `≪ π(P)/(log n)^B`, "for every fixed `B`"; parenthetical added giving the reason (band carries `≫ P/log n` primes while `π(P) ≍ Pk/log n`, so a `log P`-saving is eaten by `k ≤ K(n)`), with a pointer to §B.9 |
| 1213–1220 (§B.3 closing) | "Since `log P ≤ 2log P₀ ≤ 2log Q`, a saving `Ξ ≪ (log P)^{−A−1}` gives `≪ π(P)(log P)^{−A}`" → "Since `P ≤ π(P) log P`, a saving `Ξ ≪ (log n)^{−B−1}` gives `≪ π(P) log P (log n)^{−B−1} ≪ π(P)(log n)^{−B}`"; the forward pointer to `[B2]` retained and reworded |
| 1513–1519 (`eq:T0` + preamble) | "Fix the target saving `(log Q)^{−A}`" → "`(log n)^{−B}` of `eq:weyl`"; `T₀ := e^{80}ϱ^{10}(log Q)^{10A+40}` → `(log n)^{10B+40}`; `T₀ ≤ (log n)^{10A+50}` → `(log n)^{10B+50}` (the clause "and `log Q ≤ log n`" dropped, now unused) |
| 1522–1531 (§B.6(a)) | `F^{−1/4} ≤ (log Q)^{−(10A+40)/4} ≤ (log Q)^{−A−2}` → `(log n)^{−(10B+40)/4} ≤ (log n)^{−B−2}`; the `r ≥ 3` branch `≤ (log Q)^{−A−2}` → `(log n)^{−B−2}`; Type II line `(Fj)^{−1/10} ≤ (log Q)^{−A−4}` **by Remark `typeIIreach`** → `(Fj)^{−1/10} ≤ T₀^{−1/10} ≤ (log n)^{−B−4}` **by `eq:T0`** (citation redirected so Remark `typeIIreach`, a self-contained `(log Q)`-scale statement, needs no change) |
| 1533 (§B.6(a), `[A8′]`) | `T₀ = (log n)^{O_A(1)}` → `O_B(1)` |
| 1687 (table row 3) | `1 ≤ F < (log n)^{10A+50}` → `(log n)^{10B+50}` |
| 1791–1804 (§B.9 bookkeeping) | five occurrences `(log Q)^{−A−1}`, `(log Q)^{−A−4}` → `(log n)^{−B−1}`, `(log n)^{−B−4}` |
| 1827–1845 (§B.9, new) | **`B = 2` sufficiency check added**: `N ≫ P/log n` and `π(P) ≍ Pk/log n` give `π(P)/N ≪ k ≤ K = e^{u−u^{2/3}}`; with `J(3log H)^J = e^{O(u^{1/3} log u)}` the relative exponential-sum term is `≪ exp(u − u^{2/3} − Bu + O(u^{1/3} log u))`, which is `≤ e^{−u}` exactly when `(2−B)u ≤ u^{2/3} − O(u^{1/3} log u)`; at `B = 2` this reads `0 ≤ u^{2/3} − O(u^{1/3} log u)`, true since `u^{1/3} ≫ log u` |

Remark `typeIIreach` (1475–1481) left unchanged: it states the Type II reach
against a `(log Q)^{−A}` target with its own quantifier, remains true, and is no
longer cited by §B.6(a).

## 4. In-document records converted from open to resolved

| Location | Before → After |
|---|---|
| 1873 (§B.9 heading) | "**Open after the amendment.** Two items are recorded here rather than silently corrected…" → "**Two further items, raised by the re-indexing and now resolved in the text.**" |
| 1876–1884 (`[B1]`) | ~20-line open-mismatch entry with both candidate resolutions → one-line resolved entry: operative level set `i = 2,…,J(k)+1`, hence `F ≤ HQ^{J+1}`, `r_max = 3J+5`, `ϱ = k+3J+5`, `η′ ≥ 2^{−3J−6}`, `c = 5log2`, propagated through `eq:Jk`, `eq:xrange`, table row 1, §equi and §schedule |
| 1885–1897 (`[B2]`) | ~22-line open-mismatch entry ending "should be restated" → one-line resolved entry stating that `eq:weyl` now reads `≪ π(P)(log n)^{−B}` with `B = 2` shown sufficient, followed by the retained *why-not-`log P`* computation |

---

## 5. Certification re-verified after the edit

All four items I certified in pass 2 survive `r_max = 3J+3 → 3J+5`
(`ϱ = k+3J+3 → k+3J+5`). Each depends on `r_max` only through a term that is
already `O((loglog n)^{1/3})` or `O(log ϱ)`, set against `log Q ≥ ½e^{u^{2/3}}`,
`u = loglog n`.

1. **Lemma `dominance`, `Q ≥ 8eH e^{r_max}`.** `log(8eHe^{r_max}) = 2u + (3J+5) + O(1) ≤ 2u + 3u^{1/3} + O(1)`
   against `log Q ≥ ½e^{u^{2/3}}`. The `+2` is absorbed. The Type II variant
   (`+ log K ≤ u`) likewise. **Holds.**
2. **`T₀`.** Depends on `ϱ` only as `ϱ^{10}`; with `ϱ ≤ 2log n`,
   `T₀ ≤ e^{80}2^{10}(log n)^{10B+50}`, and `log Q ≥ ½e^{u^{2/3}} ≫ log T₀ = O(u)`.
   The two admissibility hypotheses still follow from `F ≥ T₀`:
   `T₀ ≥ e^{64}ϱ^8` (Type I, `r = 2`) and `T₀ ≥ e^{80}ϱ^{10}` (Type II) hold
   term-by-term. **Holds.**
3. **Block count.** `N_bl ≤ 1 + 2ϱ·log n/(k(k+1))` grows by `4log n/(k(k+1))`;
   estimates remain proportional to block length `≍ Q/ϱ`. Vaughan's `Q/U` term
   relative to block length needs `ϱ ≤ Q^{1/3}(log n)^{−B−1}`, i.e.
   `log ϱ ≤ log(2log n)` against `⅓log Q ≥ ⅙e^{u^{2/3}}`. **Holds.**
4. **Type II (Lemma `typeIIB`).** Two `r_max`-sensitive points:
   `M^{−2^{−r_max−2}} = M^{−2^{−3J−7}} ≤ (log n)^{−B−4}` needs
   `2^{−3J−7} log M ≥ (B+4)u`, and `log M ≥ ⅙e^{u^{2/3}}(1−o(1))` against
   `2^{−3J−7} = e^{−O(u^{1/3})}`; and `η′ log ϱ ≤ 2^{−3J−6} log(2K) = o(1)`
   (used to pass from `N_m^{−η′/2}` to `2M^{−η′/2}`). **Both hold.**
   Also the slack `ς = r(log ϱ+8)/log N ≤ (3J+5)(log ϱ+8)/(⅓log Q(1−o(1))) = O(u^{4/3}e^{−u^{2/3}}) = o(1)`,
   which is the form already printed in §B.7. **Holds.**

**Effective threshold.** Numerically, the smallest `u = loglog n` at which all
four items *plus* the §B.8 inequality `3J+6 ≤ 5u^{1/3}` hold simultaneously moves
from `u ≈ 104` to `u ≈ 115`. The certification is unchanged in kind; the
"sufficiently large `n`" threshold rises by about 10% in `loglog n`.

**One correction to my pass-2 report.** Its `[B2]` entry asserted `B ≥ 2`
suffices; I re-derived it here and it does — but only because `k ≤ K = (log n)^{1−ε_n}`
rather than `k ≤ log n`. The `−u^{2/3}` that `K` contributes is exactly what
absorbs the `O(u^{1/3} log u)` from `J(3log H)^J`. With the cruder `k ≤ log n`
the check would require `B ≥ 3`. The document now records the `K`-based version.

---

## 6. Compile

```
clean rebuild, pdflatex x2
28 pages, 536 kB
0 errors
0 undefined references
0 multiply-defined labels
0 underfull vboxes
8 overfull hboxes, maximum 9.87 pt   (0 above 10 pt)
```

Residual stale-constant sweep: `grep` for `3J+3`, `HQ^{J}`, `min{J,k}`,
`2^{-3J-4}` returns **zero** matches.

---

## 7. Open-status line

**No statement in the document remains flagged as open.** `[A1]`–`[A10]` were
discharged in pass 2; `[B1]` and `[B2]` are now applied and their §B.9 entries
read as resolutions rather than mismatches. The only items still carried as
*reported without action* are `[M4]` (Lemma `typeI` is stated for a single
monomial and applied to the band phase, the bridge being Lemma `dominance`,
which §equi cites at the point of use) and `[M5]` (the appendix and the main
text bound the small-`k` bands two different ways, both correct, the appendix's
sharper) — neither is flagged in the document, and neither was in scope for this
pass. The one substantive residual risk is unchanged from pass 2 and lies
outside the `.tex`: the Lean anchors `levelOneCarryMass_eq_band_sum` and
`levelTwoJointCarry_fiber_logMass` state the finite band form of Lemma
`measure`, whose normalization was corrected in pass 2 from `1/(k log n)` to
`1/log n`; the Lean file has not been opened and that agreement is unverified.
