# The off-diagonal term in "More than two thirds of the zeros…" is not fluctuation

*A numerical note on Prop. 5.6 of Claude/Anthropic, "More than two thirds of the zeros of the
Riemann zeta function lie on the critical line" (2026-08-10). Addressed to readers of that paper.
Every figure below is reproducible from the scripts named at the end.*

---

## 1. Claim

The paper's Prop. 5.6 controls the off-diagonal part of the prime side by an absolute-value
bound, `|O₁| ≪ L²X`. At accessible heights that bound is **loose by roughly one order of
magnitude**, and what it discards is not a fluctuating remainder. Measured directly, `O₁` is
smooth, sign-definite, and monotone, with a **cubic onset** consistent with `λ₁ = 1`:

> `O₁^main ≈ −(T·L²/6π)·(L − l₁)₊³`,  with `l₁ = l + 2·log 2 − 1`, `l = log(T/2π)`.

Zero below `λ₁ = 1`; switching on as a cubic above it. The sign is negative — the prime phases
interfere **destructively**, so the truth lies *below* the diagonal `D` alone. That is precisely
the cancellation an absolute-value bound cannot see.

Measured looseness against `L²X`, taking the implied constant as `1` (`η = 0.01`):

| | λ = 1.75 | λ = 2.00 | λ = 2.25 | λ = 2.50 |
|---|---|---|---|---|
| `\|O₁\|/(L²X)`, T = 600 | 0.123 | 0.158 | 0.126 | 0.078 |
| loose by | 8.1× | 6.3× | 7.9× | 12.8× |
| `\|O₁\|/(L²X)`, T = 1000 | 0.115 | 0.132 | 0.093 | 0.051 |
| loose by | 8.7× | 7.6× | 10.8× | 19.5× |

The factor grows with `λ`, as it must: `|O₁|` grows like `T·L²·(L−l₁)³` while the bound grows
like `L²·e^L`.

## 2. Why it matters

`λ ≤ 1` is the binding constraint on the method (§7.5(a)): *"for `X ≫ Tl` the off-diagonal terms
`O₁` are no longer dominated by the diagonal, and their evaluation would require information on
prime pairs."* That constraint comes from **bounding** `O₁`, not from the object itself.

Two observations sharpen this:

- **Prop. 2.1 is an identity.** Prime side and zero side agree at *every* `L`; nothing becomes
  ill-defined past `λ = 1`. Measured agreement `max|G^prime − G^zero| / max|G|` is
  `3.2e-11, 4.5e-11, 7.0e-11, 7.2e-11, 1.1e-10, 9.4e-11` at `λ = 0.7, 1.0, 1.25, 1.5, 1.75, 2.0`.
  The wall is in the estimation, not in the object.
- **The zero side is computable above the wall**, since it needs no primes, and there it tracks
  the `λ ≥ 1` pair-correlation branch `3λ²/(1+3λ²) → 1`. At `T = 2000, η = 0.05`, measured `C/N` =
  `0.734, 0.806, 0.871, 0.901, 0.924, 0.967` at `λ = 1, 1.2, 1.5, √3, 2, 3` against that branch's
  `0.750, 0.812, 0.871, 0.900, 0.923, 0.964`; the corresponding Prop. 4.4(ii) certificate runs
  `+0.42 → +0.57 → +0.70 → +0.76 → +0.80 → +0.89`. (The `+0.42` at `λ = 1` is the paper's own
  reading, which fixes the calibration.) `C` is stable to 6 decimals as the zero window widens
  from `[1500,4500]` to `[0,5541]`, so the zero set is adequate at every `λ` quoted.

So the payoff for evaluating rather than bounding `O₁` is large and explicitly quantified by the
paper's own machinery. **What this note does not do is collect that payoff.** Evaluating `O₁`
has been carried out from the prime side (§6) and it requires the Hardy–Littlewood conjectures —
which is the input §7.5(a) already names. The wall is where the paper says it is; what follows
measures what sits behind it.

## 3. Evidence

**Calibration.** Reproducing §8(1)'s two-sided check gives `4.5e-11` relative at `T = 600, λ = 1`,
stable under quadrature range `2000 → 60000` and step refinement — below the paper's stated
`1e-6 … 1.1e-8` band, attributable to a larger zero-set margin. That is the paper's own
diagnosis of its residual, not an inference of ours: §8(1) attributes it to *"the truncation of
the zero sum."* Independently, the measured
diagonal `D` reproduces the Prop. 5.6 formula `(T/π)Σ aₙ² g(log n)` to **0.2%** at every `λ`.

**The split.** `|O₁|/D` is `≤ 0.003` for every `λ ≤ 1.5` (`λ₁ ≤ 1.4`) — genuinely negligible below
the wall — then `0.025, 0.065, 0.113, 0.159` at `λ = 1.75, 2.0, 2.25, 2.5` (`T = 600, η = 0.01`),
and `0.024, 0.065, 0.113, 0.161` at `T = 1000`. `O₂` stays below `4e-4` of `D` throughout. The transition is **gradual**, a cubic switch-on, not a threshold.
The paper's own threshold checks out: their bound gives `O₁/D ≪ 6X/(TL)`, crossing 1 at `X ≈ T`.

**The shape.** Local log-log slope of `|O₁|` against `(L − l₁)` runs `4.34 → 3.80 → 3.42` at
`T = 600` and `3.82 → 3.50` at `T = 1000` — decreasing toward 3 from above, consistent with a
cubic plus lower-order corrections but not yet at the asymptote.

**The onset is bracketed, not pinned.** At `λ₁ = 1.014` (`T = 600, λ = 1.10, η = 0.01`) the split
gives `O₁/L² = 1.33` against `D/L² = 3395` — zero to within noise, as predicted. But `|O₁|/D`
remains `≤ 0.003` all the way to `λ = 1.5` (`λ₁ = 1.38`) and only becomes clearly nonzero past
`λ₁ ≈ 1.6`, because the cubic is extremely flat just above threshold. The data are *consistent*
with onset exactly at `λ₁ = 1` and *exclude* onset below it, but they locate it only in
`[1, 1.6]`. Claiming the onset is at `1` exactly requires the predicted form, not the data.

**The loss factor.** See the table in §1: `6.3×` to `19.5×` over `λ ∈ [1.75, 2.5]` at
`T = 600` and `T = 1000`.

> **Correction (2026-08-12).** An earlier version of this note reported this factor as `1132`
> and `1656`, i.e. "about three orders of magnitude". Those figures divided the `bound L²X`
> column of `zeta23_o1.py` by its `O₁/L²` column — **two different normalizations** — and so
> overstated the looseness by `L² ≈ 10²`. Restoring the `L²` gives the table in §1. The
> qualitative claim is unaffected: a computable main term is being discarded. The headline
> number was wrong by about two orders of magnitude and is corrected here.

**The constant is *not* pinned.** `meas/main` converges from below in all three limits and never
overshoots: `0.62 / 0.75 / 0.82` for `λ = 2.0 / 2.25 / 2.5` at `T = 1000, η = 0.01`; `0.49 → 0.72`
for `T = 300 → 2000` at `λ = 2`; `0.71 / 0.79 / 0.82` for `η = 0.05 / 0.02 / 0.01`, extrapolating
to `≈ 0.845` as `η → 0`. Naive extrapolations in `1/l`, `1/L` and `1/(λ₁−1)` all overshoot 1, so
the correction structure is not simply linear and could not be determined at accessible heights.

**Artifact checks.** The main term scales with `T` as a main term should (the ratio improves
monotonically with `T` at fixed `λ`) rather than tracking the window. The `η`-dependence is smooth
and linear — a size-`η` correction — qualitatively unlike a taper-tracking artifact.

## 4. What would be needed to use it

The averaged Hardy–Littlewood main term for `Σ_{n≠m} Λ(n)Λ(m)/√(nm)` against the paper's kernel,
with a power-saving error. Montgomery–Soundararajan's averaged singular-series estimate
`Σ_{h≤H} 𝔖(h) = H − ½log H + O(…)` is the relevant classical input.

Two warnings for anyone attempting this:

- The **averaged** statement is a theorem; **pointwise** Hardy–Littlewood is open. The obvious
  route — establish the `𝔖(h)` asymptotic for each `h`, then sum — *is* pointwise HL and is
  therefore not available. Separability must be engineered in, via the circle method or via
  large sieve / Bombieri–Vinogradov.
- Upper-bound sieve machinery (Selberg, Brun–Titchmarsh) is on the wrong side of the equation:
  it yields `≤` only, and by the parity obstruction cannot produce an asymptotic with a main
  term regardless of what is added to it.
- **The kernel's own averaging does not hand you the averaged statement.** It is tempting to
  argue that because the kernel already sums over many shifts — `|h| ≲ x/T ≈ x^{1−1/λ}`, a
  positive power of `x` for `λ > 1` — the averaged (unconditional) results apply directly. They
  do not, at least not in that form: the weights **oscillate**, `E_p` being a Dirichlet kernel
  rather than a flat average, and Montgomery–Soundararajan give no unconditional transfer against
  oscillating weights. This was attempted and could not be established; it is recorded here so
  the next person does not spend the same time on it.

## 5. What this is not

- **A proof.** It is a measurement. The numerical main term is a hypothesis about a main term.
- **A determination of the constant.** `1/(6π)` is the value consistent with the zero side; the
  measurements approach it from below without reaching it.
- **Unconditional.** *This is now the most important caveat.* The measurements are
  unconditional; the reading of `O₁` as *having* the closed-form main term of §1 is not.
  Reproducing that main term from the prime side (§6) requires the Hardy–Littlewood conjectures —
  the same input §7.5(a) identifies as missing, and the reason the `λ ≤ 1` restriction exists.
  What survives without conjecture is narrower, and is still the point of this note: `O₁` is
  smooth, sign-definite, and roughly an order of magnitude below the bound that discards it.
- **Independent of the paper's own framework — now only partly a caveat.** The closed form in §1
  was originally obtained by requiring the prime side to agree with the zero side's `λ ≥ 1`
  pair-correlation branch; since the two sides are an identity, that made it a consistency check
  rather than independent evidence. §6 discharges this for the **shape and magnitude** — the
  prime side reproduces `O₁` on its own, and produces the cubic on its own. It does **not**
  discharge it for the **constant**, which remains zero-side-derived.

## 6. Independent prime-side derivation — carried out; it does not move the wall

The derivation has been done (`tmp/zeta23_hl.py`). The headline is the second clause of that
heading, and it should be read before the numbers.

**Validation of the machinery.** Run with the true `Λ(n)Λ(m)` weights, the shift-sum machinery
reproduces the measured `O₁` to **0.4%**. So the models below differ from the measurement only in
the arithmetic weight they assume, not in the apparatus.

**Result — the prime side reproduces `O₁` with no zero-side input**, to 5–11%:

| λ | 1.75 | 2.00 | 2.25 |
|---|---|---|---|
| full Hardy–Littlewood weight `𝔖(h)`, model/measured | 0.890 | 0.955 | 0.954 |
| density-only weight `1`, model/measured | 1.485 | 0.818 | 0.579 |

stable across coefficient cutoffs (`0.967 … 0.981` for `n_min = 1, 10, 100`). *Ratios only:* model
and measurement share a normalization, the raw tables do not — see the trap in §7.

**The shape is reproduced independently.** The model's *own* local log-log slope of `|O₁|` against
`(L − l₁)` runs `4.65 → 3.83` across `λ = 1.75, 2.0, 2.25` — the same descent toward 3 seen in the
measurement (§3). The cubic and its onset therefore come out of the prime side; they are not
artefacts of having imposed the zero side's branch.

**Density alone is not enough, and this is the finding that matters.** The density-only model is
not merely less accurate — it is *inconsistent*: `1.485, 0.818, 0.579`, drifting monotonically
with `λ` and collapsing to `0.42` once small `n` are excluded. Genuine prime-pair information is
required. Any hope that the main term is reachable from the density of `Λ` alone is closed off.

**So the dependency is relocated, not removed.** Evaluating `O₁` needs Hardy–Littlewood — exactly
the input §7.5(a) names as the reason for the `λ ≤ 1` restriction. Pinning the boundary at source
(Montgomery–Soundararajan, arXiv math/0409258): their **Theorem 2, the average of the singular
series, is unconditional**, and the machinery here reproduces `𝔖`'s local factor at 3 as `1.9992`
against the exact `2`. But the transfer to primes — statements about `Σ_n Λ(n)Λ(n+h)` — requires
their hypothesis (20) (`E_k(x;D) ≪ N^{1/2+ε}`) or the k-tuple conjecture. Their unconditional
Theorem 1 is a moment *bound*, not the asymptotic. **The common mode is computable modulo
Hardy–Littlewood — the same conjecture the bound was avoiding.**

**The constant is still not independently predicted.** The model is a finite-`T` numerical
evaluation: it reproduces the *measured* `O₁`, but model and measurement both sit at 59–72% of the
asymptotic closed form of §1. Obtaining `1/(6π)` from the prime side needs the model's asymptotic
evaluation, which has not been done.

**A predicted-in-advance analytic route that failed.** Writing `𝔖 = 1 + (𝔖−1)` was expected to
annihilate the density-1 part, it being the kernel's Fourier transform at frequency `m̄ ≈ T ≠ 0`;
the whole main term would then have come from the singular series' deviation, which would have
explained the negative sign. **The prediction is false.** The density-1 model measures 82% of the
total, not 0 — the Poisson aliasing terms survive because `x` ranges up to `X ≫ T`. What stands is
a numerical prime-side model, not a pen-and-paper derivation.

**The averaged model was run, and it fails.** The decisive question is whether the *averaged*
singular series — the unconditional input — suffices. It does not. Weight
`M3 = 1 − 1/(2|n−m|)`, i.e. density plus the Montgomery–Soundararajan secondary term, does not
reproduce `O₁`. Ratios to the measured value at `T = 600, η = 0.01`, every sum carried to
`h ≤ 200` where all four models have converged (`tmp/zeta23_m3.py`, `tmp/zeta23_m3conv.py`):

| model | arithmetic input | λ = 1.75 | λ = 2.00 |
|---|---|---|---|
| EXACT, weight `Λ(n)Λ(m)` | none — validation gate | 1.022 | 1.000 |
| `M2`, weight `𝔖(h)` | full Hardy–Littlewood *(conjectural)* | 0.897 | 0.958 |
| **`M3`, weight `1 − 1/(2h)`** | **averaged `𝔖` — *unconditional*** | **1.082** | **0.871** |
| `M1`, weight `1` | density only | 1.429 | 0.803 |

Normalised by the gate, `M2` varies by **9%** across the two `λ` (0.878 → 0.958), `M3` by **22%**
(1.059 → 0.871), and `M1` by **74%** (1.398 → 0.803). **`M3` fails in the same manner as the
density model** — overshooting at the lower `λ`, undershooting at the higher, drifting in the same
direction — merely less severely. Only the pointwise `𝔖` reproduces `O₁` stably.

This settles the question in the negative: **the gap to full Hardy–Littlewood is real, and it is
the pointwise arithmetic of `𝔖` that closes it.** The mechanism is visible in the construction —
`M3` discards `𝔖`'s parity (`𝔖(h) = 0` for odd `h`) and its local factors at odd primes, while the
kernel `E_p(θ)` oscillates with `θ = log(n/m) ≈ h/n` and so does not average that structure away.
That is the warning of §4 in numerical form: averaged results do not transfer against oscillating
weights. It was previously an argument that could not be completed; it is now a measurement.

*The `λ = 2.25` row is omitted deliberately.* At `h ≤ 60` its gate reads `1.178` — the `h`-sum is
truncated at the larger `X` — and a model whose validation gate is 18% off certifies nothing. The
two rows above are reported because their gates are `1.022` and `1.000`.

## 7. Reproduction

Scripts in `tmp/`: `zeta23_prime.py` (`ν_X`, prime powers, the ambiguity function in all three
regimes), `zeta23_twosided.py` (prime vs zero side), `zeta23_o1.py` (reference `D`/`O₁`/`O₂`
split), `zeta23_o1_fast.py` (BLAS split, `T`-scaling, taper modes).

Saved outputs backing the tables above: `tmp/O1_NOTE_twosided.txt` (`zeta23_twosided.py`),
`tmp/O1_NOTE_o1_T1000_eta01.txt` and `tmp/O1_NOTE_o1_T600_eta01.txt` (`zeta23_o1.py T η`),
`tmp/O1_NOTE_lambda.txt` (`zeta23_lambda.py`, the `C/N` and certificate table in §2).

**Normalization trap — read before re-deriving from the raw tables.** `zeta23_o1.py` prints
`O₁/L²` and `L²X` in *different* normalizations. Dividing those two columns directly overstates
the looseness by `L² ≈ 10²`; that is the error corrected in §3. For the same reason the fitted
main term applies to `O₁/L²`, which is why the `L²` appears explicitly in the formula in §1.

**Citations checked against the paper** (35 pp., verified 2026-08-11). The paper is not on arXiv
and is not in the Lean artifact repository; it is hosted at
`www-cdn.anthropic.com/564f962e60643842f5fcb4a17c9dbc8f608f1c37.pdf`, linked from
`anthropic.com/research/riemann-zeta`. A local copy is at `refs/zeta23_paper.pdf`. Every
reference used above was read at source:

| cited here | as it appears in the paper | |
|---|---|---|
| Prop. 5.6, error `O(L²X)` | `M[P_X,P_X] = (T/π)Σ aₙ² g(log n) + O(L²X)` | ✓ |
| §7.5(a), the `λ ≤ 1` quote in §2 | §7.5 "Limits of the method", (a) "Dimension" | ✓ verbatim |
| §8(1), the `1e-6 … 1.1e-8` band | "between `10⁻⁶` and `1.1·10⁻⁸`" | ✓ |
| Prop. 2.1, "prime side = zero side is an identity" | "Explicit formula, spectral form"; the two expressions of (2.20) "agreeing by Proposition 2.1" | ✓ |
| the `cert` column in §2 | defined in §8(2) as `(2C − N(I′))/N(I)`; the underlying inequality is Prop. 4.4(ii) | ✓ |

`(5.12)` was listed in an earlier draft of this section but is not relied on anywhere above, and
has been dropped rather than cited unused.

*Extraction note:* `pdftotext -layout` splits superscript exponents onto the preceding line, so
`10⁻⁶` reads as a bare `10`. Do not mistake that for a missing exponent.

Two implementation traps, both silent, both caught only by validating against direct quadrature:
the ambiguity-function identity `∫φ̂(τ−τ_k)φ̂(τ−τ_l)cos(τ log n)dτ = 2π R(log n, δ)cos(m̄ log n)`
requires `w ≤ u ≤ L − 2w`; the lower guard fails for `n = 2` unless `ηL ≤ 2 log 2`, and the upper
guard fails for primes near `X` (~4000 of them at `λ = 2`, carrying ~4% of the sum), needing panel
Gauss–Legendre across the ramp corners. Both regimes now agree with the slow reference to `1e-13`.
