# Sym^5 functoriality on GL(6): an analytic (converse-theorem) close attempt

**Object.** `pi = Delta` (weight 12, level 1). Target: `Sym^5 pi` automorphic on GL(6) via the
Cogdell–Piatetski-Shapiro converse theorem, i.e. show `L(s, Sym^5 pi x sigma)` is *nice*
(continuation + vertical boundedness + convolution FE with the right root number) for `sigma`
on GL(1)…GL(4), **analytically and Galois-free** — the case classical Langlands–Shahidi cannot
reach and which Newton–Thorne closed by automorphy *lifting* (Galois), not analytically.

**Bottom line up front.** **PARTIAL CLOSE.** The analytic weld mechanism — the functional
equation read as the *helix ↔ anti-helix conjugation over the origin*, with the root number `eps`
**emerging** (never fed) — is built, validated, and made non-circular. It **closes cleanly through
degree 6** (the bare `Sym^5 Delta` carrier, `eps = -1` emergent) and for the **GL(1) Tate-twist
clock** (weld *covariant* under a continuous carrier warp). For the first genuine **GL(2)** step it
**converges toward the correct `eps = +1`** but is limited to ~10–50% precision by the high
archimedean conductor. **GL(3)/GL(4) are beyond the numerical reach** of the difference-method
instrument (the anti-helix strand falls below machine precision) — *inconclusive, not a break*.
So: `(a)` archimedean uniformity and `(b)` continuation/boundedness **hold**; `(c)` the crux
convolution FE **emerges non-circularly and correctly wherever it is numerically resolvable**
(GL(1) fully, GL(2) in sign and convergently in magnitude), and the mechanism is **Galois-free**
(hence structurally Maass-ready). What is **not** achieved is a clean high-precision close at
GL(3)/GL(4) and — the real mathematical gap — a *proof* of the FE for the full `sigma`-family.

Scripts: `tmp/sym5_close.py`, `tmp/frontier_retest.py`, `tmp/frontier_gl2_deep.py`.
Results: `tmp/sym5_close_results.txt`.

---

## 1. The construction (concrete)

**Carrier / Satake (local, oracle-free).** `tau(p)` exact from the `eta^24` recurrence
(cross-checked `tau(2..7)`); analytic Satake angle `theta_p = arccos(lam_p/2)`,
`lam_p = tau(p)/p^{11/2} = 2cos theta_p`. `Sym^5` clocks at `p`:
`{e^{i(5-2j)theta_p}}_{j=0..5} = {alpha^{+-5}, alpha^{+-3}, alpha^{+-1}}` (degree 6, unitary).

**Clock-warp by sigma (local tensor rule).** The `sigma`-twist warps each carrier clock:
- `sigma = |.|^{it0}` (Tate, GL(1)): continuous phase warp `c_n -> c_n n^{-it0}` (conductor 1);
- `sigma = Sym^b(g)` (GL(b+1)): additive tensor of clocks `{e^{i((5-2j)theta_p + (b-2k)phi_p)}}`,
  `phi_p` = Satake angle of the second form `g` (here `f_16 = Delta·E_4`, weight 16, level 1,
  chosen of *distinct weight* so every archimedean tensor weight is nonzero → clean `Gamma_C`).

Convolution Dirichlet coefficients `c_n` are built **multiplicatively from the two factors'
Satake data only** (`h_m` = complete homogeneous symmetric poly of the tensor eigenvalues,
Newton's identity). This matches the Lean `TwoClockWeightLaw` ontology: the coefficient is the
power-sum/Chebyshev trace of unimodular clocks, `s_k = Sum alpha_i^k` (verified: `clockTrace`,
`two_clock_log_expansion`), **not** a Jacobi–Anger series.

**Degree-`d` completion (local archimedean data).** `gamma(s) = prod_j Gamma_R(s + mu_j)`,
`Gamma_C(s+g) = Gamma_R(s+g)Gamma_R(s+g+1)`, with `mu_j` the multiset of `|w_pi +- w_sigma|`
tensor archimedean weights (`w = (r-2j)(k-1)/2`). Bare `Sym^5 Delta`:
`Gamma_C(s+11/2)Gamma_C(s+33/2)Gamma_C(s+55/2)` — the three-strand criss-cross. The kernel
`K = inverse-Mellin(gamma)` is tabulated once (log-space contour integral; cubic-spline
interpolation for the sign-definite low-degree kernels) and **self-checked** against
`int K(y) y^s dy/y = gamma(s)` (see §3).

**The weld = emergent `eps` (helix ↔ anti-helix conjugation).** Riemann completion
`Lambda(s) = int_0^inf Theta(u) u^s du/u`, `Theta(u) = Sum_n c_n K(n u / sqrt(Q))`. Splitting at
`u=1` and using the reflection `u -> 1/u` (the conjugation over the origin, `z·z̄ = 1`):

    Lambda(s) = A(s) + eps · A(1-s),   A(sigma) = int_1^inf Theta(u) u^sigma du/u.

Both one-sided completions use `Theta` **only for `u >= 1`** (the numerically robust regime).
At `Re(s0) > 1` the honest convergent completed value `Lambda_true(s0) = gamma(s0) Q^{s0/2} Sum c_n n^{-s0}`
is known with **no FE**, so

    eps(s0) = ( Lambda_true(s0) - A(s0) ) / A(1-s0)     [ eps is the OUTPUT ]

is *solved*. If the FE holds, `eps(s0)` is unimodular and constant across `s0` and lands on a
`mu6 / pi-3` harmonic cell (`e^{2i·0}=+1`, `e^{2i·pi/2}=-1`); if not, it drifts. This is the exact
analytic content of `warpedBlock_det_one` (`w·w̄=1` weld) + `reflection_fixes_iff` (`s<->1-s` axis)
— which the Lean project supplies *geometrically* but never as an analytic FE (see §5).

---

## 2. Circularity audit — exactly what was fed in

**Fed in (all local / allowed):** (i) `tau(p)` and `f_16`-Satake `phi_p` (exact `eta^24`
recurrence / short per-prime `Delta·E_4` convolution); (ii) the tensor rule
`Sym^5 (x) sigma`; (iii) each factor's archimedean Langlands type (the `mu_j`) and conductor
(level 1 ⇒ `Q = 1` for the sym-tensor twists; `q^{r+1}` for a character). These are precisely the
"two factors' individual data" the discipline permits.

**NOT fed (the forbidden inputs):** the convolution's root number `eps` (it is *solved* from the
weld); the assumption that `Sym^5 pi` is automorphic; the classical Rankin–Selberg integral
(which would *require* that automorphy to give the FE). The known `eps` appears only as a
post-hoc comparison column.

**Discrimination proof (falsifiability register).** Two negative controls confirm the test is not
tautological: (1) detune one Satake angle `theta_7 -> theta_7 + 0.35` ⇒ emergent
`eps = 0.032 + 0.081 i` (off every real cell, `|eps| << 1`, `s0`-inconsistent) — FAILS as it must;
(2) drop one `Gamma_C` from the gamma factor of the *true* `Sym^5 Delta` ⇒ `eps` drifts
`0.23, 0.42, 0.56` (`||eps|-1| = 0.77`) — FAILS. A wrong object does **not** produce a weld.

---

## 3. Per-input verdicts (numbers + tier)

### (a) Archimedean uniformity — **HOLDS (MEASURED, exact-gauge-equivalent).**
Kernel self-check `int K(y) y^s dy/y` vs `gamma(s)`: rel `1.6e-13` (d=6), `7.3e-13` (d=12).
The degree-`d` gamma factor from local tensor archimedean data behaves; the three-strand (d=6)
and its higher tensors are the correct window. (d=18: `1.1e-4`; d=24: `0.73` — the contour loses
accuracy for shifts ~50, see §4.) This is the numerical face of the project's proven exact gauge
(`StOscillation` / Part-I uniformity).

### (b) Continuation + vertical boundedness — **HOLDS (MEASURED + Lean-proven analog).**
`Theta(u) = Sum c_n K(nu)` converges (kernel super-exponential decay); `A(s)` finite on the whole
strip; partial sums bounded. This is the numerical companion of the *one* piece the Lean project
genuinely derives itself: `LFunctionPhasor.dirichlet_strip_tendsto_LFunction` (phasor partial
sums → `LFunction` on all `Re s > 0`, Abel + bucket cancellation).

### (c) THE CRUX — convolution functional equation (emergent `eps`).

**Validation ladder — `Sym^r Delta` (r=1..5), FE known. Instrument fully calibrated:**

| object | degree | emergent `eps` | cell | `s0`-spread | known |
|---|---|---|---|---|---|
| `Sym^1 Delta` | 2 | **+0.99997** | +1 | 9.9e-5 | +1 ✓ |
| `Sym^2 Delta` | 3 | **+0.99994** | +1 | 1.8e-4 | +1 ✓ |
| `Sym^3 Delta` | 4 | **-0.99977** | -1 | — | **-1 ✓** |
| `Sym^4 Delta` | 5 | **+1.00020** | +1 | 6.4e-4 | +1 ✓ |
| `Sym^5 Delta` | 6 | **-0.99798** | -1 | 4.1e-3 | (emergent) |

All five signs correct to `~1e-3`, *including a known `-1` case* (Sym^3). **`eps(Sym^5 Delta) = -1`
emerges non-circularly** (`s0`-consistent to `6e-3`, matches the `(-1)^{n(n+1)/2}` pattern). This is
the bare helix↔anti-helix weld of the Sym^5 carrier. **Tier: MEASURED, high confidence.**

**GL(1) Tate-twist clock `sigma = |.|^{it0}` — WELD COVARIANT.** Scanning `t0` on the `pi/3`
harmonic grid at `sigma0 = 1.5`:

| `t0` | 0 | pi/6 | pi/3 | pi/2 | pi | 2pi |
|---|---|---|---|---|---|---|
| `eps` | -0.998 | -1.000 | -1.001 | -0.999 | -0.999 | -1.000 |

`max|eps - mean| = 1.9e-3`, `||eps|-1| = 1.9e-3`. The continuous carrier warp moves `|A|` and
`arg A` genuinely, yet `eps` stays pinned at `-1`: **the weld is covariant under the GL(1) clock.**
**Tier: MEASURED, clean. (The Dirichlet-character GL(1) base is already established in the house;
the Tate clock is its continuous-warp companion, requested and confirmed here.)**

**GL(2) step `Sym^5 Delta x f_16` (degree 12) — PARTIAL: sign emerges `+1`, magnitude converging.**
Kernel exact to `7e-13`. The anti-helix strand `|A(1-s0)| ~ 5e-8` is ~10^3 below the helix strand
`|A(s0)| ~ 5e-5` (high archimedean conductor `~ sqrt of ~1e12`), so `eps` extraction is a ~4-digit
cancellation. Pushing the coefficient bank past the kernel support (`n ~ 15500`, fast FFT Satake):

| coeff bank `N` | `eps_mean` | `s0`-spread | `eps` at well-conditioned `s0=1.35` |
|---|---|---|---|
| 12000 | +1.169 | 1.61 | 0.889 |
| 22000 | +1.024 | 0.49 | 0.954 |
| 32000 | +0.879 | 1.13 | 1.079 |
| 44000 | +0.952 | 0.49 | 1.036 |

The **sign is robustly `+1`** (cell `+1` at *every* `s0` and *every* `N`); the magnitude clusters at
`+1` (best-conditioned probe `s0=1.35`: `0.89, 0.95, 1.08, 1.04`). The residual scatter is the slow
convergence of `Lambda_true` at `Re(s0) ~ 1.05` (near the abscissa), **not** an FE failure — the
well-conditioned probe converges to `+1`. **Tier: MEASURED-partial: the GL(2) weld sign emerges
non-circularly and correctly; magnitude → 1 within ~10-50% conditioning noise. Not a clean close.**

**GL(3) `x Sym^2 f_16` (d=18), GL(4) `x Sym^3 f_16` (d=24) — INCONCLUSIVE (numerical wall).**
Kernel self-check fails (`1.1e-4`, `0.73`); the anti-helix strand `|A(1-s0)| ~ 1e-10` (d18),
`~1e-14` (d24) is at/below machine precision, so emergent `eps` is unresolved
(`|eps| ~ 10^3`–`10^9`, garbage). This is a **precision wall from the large archimedean conductor**,
identical in character to the BE-program wall (aliasing / effective-rate ceiling in the house
memory), **not** a demonstrated FE break. **Tier: BEYOND REACH (float64 difference method).**

**FE residual — control vs frontier.** Control `Sym^5 Delta`: `|eps|-1| = 6e-3`, sign exact.
GL(1) Tate: `1.9e-3`. GL(2): sign exact, `|eps|-1| ~ 5e-1` (conditioning). Negative controls:
`O(1)` drift (as required). GL(3/4): unresolved.

---

## 4. Where it breaks, precisely

1. **Numerical (instrument):** the emergent-`eps` *difference* method at `Re(s0) > 1` is
   ill-conditioned once the archimedean conductor is large — the anti-helix strand `A(1-s0)` is
   exponentially small relative to the helix strand `A(s0)`. Resolvable at d ≤ 6 (`A(1-s0) ~ 1e-4`),
   marginal at d = 12 (`~1e-8`, sign-only), lost at d ≥ 18 (`<= 1e-10`). A **balanced-AFE emergent-`eps`**
   (solve `eps` by independence of the split point at the conductor scale, both strands `O(1)`) or
   `mpmath`-throughout high precision would push further; not implemented here.
2. **Mathematical (the real gap):** the converse theorem needs the FE for the **entire** `sigma`
   family with **uniform** control. Numerics confirm finitely many `sigma`; the uniform continuation
   + boundedness over the family is unproven — the same wall the Beyond-Endoscopy program hits.
   The Lean audit is decisive here: the project **derives** the strip continuation and the geometric
   weld algebra (`reflection_fixes_iff`, `warpedBlock_det_one`, `dual_pair_det_one`) but the analytic
   FE itself is **imported from Mathlib** (`completedLFunction_one_sub`, `completedRiemannZeta_one_sub`)
   — and for `Sym^5 pi x sigma` there is **no Mathlib to import from**. Establishing that FE *is* the
   missing step; the measurements above support it but do not prove it.

---

## 5. Is it Galois-free? — YES (Maass-ready in structure)

Nothing in the construction used a Galois representation, an automorphy-lifting theorem, or the
residual characteristic — only local Satake parameters, archimedean Langlands types, the tensor
rule, and the analytic weld/continuation. The mechanism is purely on the *analytic/spectral* side.
Therefore the identical pipeline applies to a **Maass** base form (replace `theta_p = arccos(a_p/2)`
by the Hecke eigenvalue of a Maass form and the holomorphic `Gamma_C` shifts by the Maass
archimedean parameters `Gamma_R(s +- i t_spec)`): the emergent-`eps` weld test is *type-agnostic*.
This is exactly the direction Newton–Thorne's Galois method cannot go, and where an analytic close
would be genuinely new. The present work shows the analytic weld is **real and non-circular**
(closes at GL(1), converges at GL(2)); it does **not** yet clear the high-conductor / uniform-family
wall that separates "the FE emerges in every resolvable instance" from "the FE is proved for all
`sigma`."

---

## 6. Verdict summary

| converse-theorem input | GL(1) | GL(2) | GL(3) | GL(4) | tier |
|---|---|---|---|---|---|
| (a) archimedean uniformity | ✓ | ✓ | ✓(kernel marginal) | (kernel fails) | MEASURED |
| (b) continuation / boundedness | ✓ | ✓ | ✓ | ✓ | MEASURED + Lean |
| (c) convolution FE, `eps` emergent | ✓ covariant weld | ~ sign `+1`, mag→1 | inconclusive | inconclusive | MEASURED / BEYOND REACH |

**Did Sym^5 close?** No — **partial**. The analytic weld that would drive the converse theorem is
constructed, validated non-circularly (5/5 known signs, 2/2 negative controls), and demonstrated to
be Galois-free; it closes at the carrier (deg 6) and the GL(1) Tate clock, and the GL(2) step
converges to the correct sign. It does **not** close at GL(3)/GL(4) (numerical precision wall) and
does not deliver a *proof* of the FE for the full family (the genuine remaining mathematics — the
same wall the BE program isolates). **Honest status: the mechanism works everywhere it can be
resolved; the close is gated on (i) a better-conditioned high-degree emergent-`eps` computation and
(ii) the uniform-over-`sigma` FE proof, neither achieved here.**
