# Transplanting the Chirre–Gonçalves–de Laat certificate into the Sylvester compression frame

*Working note, 2026-08-12 (RH ledger attempt 028). Status — REVISED SAME DAY: the §2
Fejér–Riesz architecture below is **refuted** (see §2a): the u-side modulus forces
single-family Frobenius kernels into `{ĝ = w⋆w : w ≥ 0}`, which cannot dip. The LP value
of §3 stands as the value of the band-limited CGdL class; the live route to realize it is
the termwise strip-positivity certificate of §4a (attempt 028b). Companion to
`O1_LOSSY_NOTE.md`; scripts in `tmp/att027_*.py`, `tmp/att028_cgdl_verify.py`.*

## 1. Claim under construction

Unconditionally, at least `2 − Z*(2) − o(1)` of the zeros of ζ in `(T, 2T]` are simple and
on the critical line, where `Z*(2) ≈ 1.3211` is the Chirre–Gonçalves–de Laat optimum
restricted to kernels of Fourier type 2. Numerically `2 − Z*(2) ≈ 0.6788`, against the
current record 0.6725 (zeta23 Theorem D = Montgomery–Taylor made unconditional, 2026-08-10).

The composition is of three published pieces, none of which has been combined before:

1. **CGdL (Adv. Math. 2020, arXiv:1810.08843).** On RH: `N*(T) ≤ (1.3208+o(1))N(T)`,
   hence ≥ 0.6792 simple zeros, by minimizing `Z(g) = ĝ(0) + ∫₋₁¹ ĝ(x)|x| dx` over
   auxiliary `g` with `g ≥ 0` on ℝ, `g(0) = 1`, and `ĝ ≤ 0` off `[−1,1]`. The mass of
   `ĝ` outside the band is discarded **by sign** against `F ≥ 0` — no evaluation there.
   Montgomery–Taylor (`Z = 1.3274993`) is the sub-case `supp ĝ ⊆ [−1,1]`.
2. **BGSTB (Acta Arith. 2024, arXiv:2306.04799), Theorem 1.** Unconditionally, the pair
   form `F(α)` (all complex zeros, `(ρ, ρ̄′)`-pairing) is *real, even, nonnegative for
   every real α* — a perfect square — and equals Montgomery's asymptotic on `[0,1]`.
   RH entered CGdL only through (a) this band evaluation and (b) the zero-side reading;
   (a) is therefore free.
3. **zeta23 (2026-08-10), §§3–4.** The zero-side reading (b) — the only remaining RH
   step — is replaced by Sylvester inertia + the rank–trace inequality (their Lemma 3.2),
   *provided* the kernel is realized as a Gram matrix of a Gabor-type family. They ran
   this only for window-square kernels, which is exactly the `supp ĝ ⊆ [−1,1]` subclass;
   hence their Theorem D cap at Montgomery–Taylor.

## 2. The dictionary (this is the work)

zeta23's Frobenius norm is a pair sum against the kernel `Φ²` in the ordinate-difference
variable, whose transform lives in the log/`u` variable: `Φ(z)² = ∫ g(u)e^{izu}du`,
`g = φ²⋆φ²`, `supp g ⊆ [−L, L]`, `x := u/l`. In CGdL coordinates:

| CGdL | zeta23 |
|---|---|
| `g` (≥ 0 on ℝ, ordinate differences) | `Φ²` (a square — hence ≥ 0) |
| `ĝ` (x-space, spike + ramp measure) | `φ²⋆φ²` (u-space, band-limited) |
| `ĝ(0)`-spike term | the `μ²`/density term (`1/λ₁` in their (5.13); Fejér at support λ has `ĝ(0) = 1/λ` ✓) |
| `∫ĝ(x)|x|dx` | the prime term (`λ₁/3` ✓) |
| `g(0) = 1` | the (4.4) unit normalization (`a²`-corrections) |

So their class is "kernels that are squares of band-limited functions" and CGdL's is
"nonnegative kernels with a sign condition beyond the band". The bridge is classical:

**Fejér–Riesz / Krein.** A nonnegative integrable kernel of exponential type `2l`
factors as `g_eff = |Ψ|²` on ℝ with `Ψ` of type `l` (Boas §7.5; Paley–Wiener gives
`Ψ`'s transform one-sided support of length `2l`, recentered to `[−l, l]` by a
modulation, which only re-phases the Gabor grid).

**The family.** Take `f_k(u) = ψ(u)e^{−iτ_k u}` with `ψ = Ψ`'s transform and grid
spacing `h = π/l` — *doubled* critical density, matched to the doubled band. Poisson
then has **no aliasing** (the aliasing frequencies sit at `±2l`, the boundary, where the
transform vanishes), so:
- Lemma 2.2's identity survives: the per-zero full-grid weight is a constant, giving
  the (4.4) units in which an isolated on-line zero has eigenvalue `m_ρ`;
- the identity continues analytically, so `tr Â_Ψ = N` **for every configuration**
  (same mechanism as their Remark 5.10's configuration-independent trace);
- §4 ports verbatim: on-line zeros give PSD rank-one blocks (now Hermitian — `Ψ`
  complex — inertia theory unchanged), off-line pairs give signature-(1,1) blocks,
  and Lemma 3.2 needs only a Hermitian matrix.

**The Frobenius split.** With `ĝ₂ := −ĝ_eff·1_{(1,2]} ≥ 0` and `K₂` its kernel:

    ‖Â_Ψ‖²_F  =  S(g_eff)  =  S(g_eff·band) − S(K₂),
    S(K₂)      =  ∫ ĝ₂(x) |Σ_ρ m_ρ e^{ixlγ_ρ}|² dx  ≥  0,

a five-line perfect square in the same `(γ_ρ, γ̄_ρ′)`-pairing as Weil's form — valid for
complex ordinates, multiplicities included (this is BGSTB's Lemma 3 mechanism; for the
windowed `A`-matrix it is self-contained and needs no import). So

    ‖Â_Ψ‖²_F  ≤  S(g_eff·band)  =  (Z(ĝ_eff) + o(1))·N,

the band part being their own §5 computation: Prop 5.6's proof used only band-limitation
`≤ l`, the Montgomery–Vaughan inequality, and kernel regularity — nothing about the
kernel being a window-square. Lemma 3.2 then gives, unconditionally,

    3s₁ + 4s₂ + 4p  ≥  4N − Z·N − o(N)   ⟹   s₁ ≥ (2 − Z − o(1))N.

## 3. The value Z*(S), computed (validated controls)

Exact convex formulation (`tmp/att027_sdp.py`): atomize `ĝ` at spacing `Δ` on `[0, S]`;
`g ≥ 0` on ℝ is *exactly* the Fejér–Riesz/Toeplitz PSD condition on the atom sequence
(no constraint grids); the spike term is the `ĝ`-**density** at 0, i.e. `c₀/Δ`.

| class | value | source |
|---|---|---|
| Fejér (Montgomery) | `4/3 = 1.3333` | direct |
| `S = 1` LP, Δ=0.04/0.02/0.01 | `1.3270103 / 1.3273770 / 1.3274687` | **positive control: O(Δ²) → 1.3274993 = Montgomery–Taylor** ✓ |
| `S = 2` LP, Δ=0.04/0.02 | `1.3207926 / 1.3210705` (CLARABEL), `1.3210869` (SCS) | Richardson ⟹ continuum `Z*(2) ≈ 1.3212` |
| CGdL, unrestricted type | `1.3208` | their paper (RH case) |

The type-2 restriction costs only ≈ 0.0004 of CGdL's 0.0067 gain: **the entire mechanism
survives band-limitation**, and `2 − Z*(2) ≈ 0.6788`.

Two instrument traps, recorded for reuse:
- the spike term reads the `ĝ`-density at 0; atomizing it deletes the `μ²`-term silently
  (the Fejér gate read 0.37 instead of 4/3 — the gate caught it);
- finite cutting-plane relaxations of `{g ≥ 0}` cannot see `∫g > 0` and the LP runs
  unbounded; the Toeplitz-PSD reformulation is exact, and its `c₀ = mean(g) > 0` is
  precisely what the cutting planes could not express.

## 2a. REFUTATION of §2's architecture (same day, by the §4 harness)

The matrix-level harness (`tmp/att028_cgdl_verify.py`) returned negative slack on every
configuration and cert/N = +1.11 > 1 — impossible — and tracing the discrepancy exposed
a structural error in §2: the Frobenius pair-kernel of a Gabor family with window `ψ` is
the transform of `|ψ(u)|²`, and the **modulus is forced by the norm structure**. Hence
the pair-kernels realizable by a single compression are exactly

    { ĝ = w ⋆ w  :  w ≥ 0, supp w ⊆ [−l, l] }

— autocorrelations of nonnegative functions, which are pointwise nonnegative. **The CGdL
dip cannot be realized by any single family, with any window, complex or not.** This is
the true content of zeta23's Theorem D cap: Montgomery–Taylor is the exact optimum of the
realizable class (their §7.1 optimization over `v = φ²` *is* the full `w ≥ 0` class).
The Fejér–Riesz step in §2 factorized the ordinate-difference side — which was never the
obstruction — while the u-side modulus is. Two-family cross terms `tr(A₁A₂†)` do produce
sign-mixed autocorrelations `h⋆h̃ᶜ` (h complex), but no counting inequality is known for
them; that remains an open linear-algebra question.

**Method law (reusable):** before claiming a kernel class is realizable by a
quadratic-form construction, check which side of the Fourier pair the construction forces
nonnegative.

## 4a. The repair: a termwise strip-positivity certificate (attempt 028b, live)

Drop the matrix machinery entirely and run Montgomery's original integrality argument
configuration by configuration. Unconditionally, `N* ≤ S(g)`-normalized requires the
kernel's zero-side terms to dominate the diagonal termwise:

- on-line × on-line off-diagonal: `g ≥ 0` on ℝ (as before);
- pair sites `{ρ, 1−ρ̄}` at depth `y`: the four terms give `2m²(1 + Re g(2iy·scaled))`,
  needing `Re g(2iy·) ≥ 0` — the `v = 0` slice of:
- on-line × pair and pair × pair cross terms: **`Re g(v + iw) ≥ 0` for all real `v` and
  `|w| ≤ 2y_max`** (scaled) — strip positivity of `Re g`.

Pairs deeper than `y = A/log T` are `≪ e^{−cA} N` by **Selberg's density theorem
(1946, unconditional)**; exclude them from the certificate and charge the loss. The new
extremal problem: minimize `Z` over the §3 class plus the strip constraints at scaled
half-width `2A`. In atoms, each `w`-slice is again an exact Toeplitz-PSD condition on the
cosh-weighted sequence `c_j cosh(x_j w)` — the SDP extends with one PSD block per
`w`-sample. Final constant: `2 − Z(A) − C e^{−cA}`, optimized over `A`. `Z(0⁺) = 1.3212`;
computing `Z(A)` is the immediate next step. Note the prize shrinks but the proof
*simplifies*: the zero-side is elementary (integrality only), the band evaluation is
BGSTB/Montgomery, and the only structural inputs are strip positivity (LP-certified) and
Selberg's density theorem.

## 4. Proof obligations of the (refuted) §2 route — kept for the record

* **(α) Factorization with regularity.** Fejér–Riesz factor of the (mollified) optimal
  kernel; mollify in the ordinate-difference variable (multiplies `g` by a positive
  function — sign preserved; smears `ĝ` at the dip edge — run the final optimization
  with the dip from `x = 0.98` as margin). Need `ψ` regular enough for the tail estimate.
* **(β) Doubled-density bookkeeping.** Poisson/units at `h = π/l` (aliasing at the
  vanishing boundary); trace evaluation (the prime part of the trace is a single
  `Λ`-sum against a constant kernel — integrates to `o(N)`); tail estimate Prop
  4.2-analog (unchanged: `Ψ` has type `l`, so `θ₀ ≍ l T^{−1/2}`).
* **(γ) Band evaluation for a general kernel + spike reading.** §5 with `Φ²` replaced by
  a general C¹ band-limited kernel (their proof structure ports); the `o(1)` of reading
  the `T^{−2|x|}log T` spike against `ĝ_eff(0)` (CGdL Lemma 8-style).
* **Verification pending:** matrix-level synthetic-configuration harness (their §8(5)
  style: doubles, deep pairs, near-extremal lattices); end-to-end certificate on true
  zeros vs the Fejér baseline at matched height; final rational/interval-certified
  feasible `ĝ` (CGdL's own verification format).

## 5. What this is not

- **A theorem.** The obligations of §4 are open until written out. The constant
  `0.6788` is the LP value, not yet a certified one.
- **In tension with zeta23's ceiling.** Their Remark 1.1 cap (0.68185) binds
  certificates reading bandwidth-1 two-moment data; this certificate reads sign data on
  `(1, 2]`, which their §1.2 explicitly places "in a different regime". (`0.6788 <
  0.68185` anyway.)
- **A route to RH.** Like everything in this class it is insensitive to `o(N)` off-line
  zeros (their §1.5); the gap to 1 stays structural. The `λ ≤ 1` prime-pair wall
  (`O1_LOSSY_NOTE.md`) is untouched: the `(1,2]` region is used for *sign*, never
  evaluated.

## 6. Distinct zeros

The same transplant applied to CGdL's Corollary 3 machinery (their RH value 0.8477
distinct) against zeta23's Theorem C (0.83625) should move the distinct-zeros record
similarly; not yet set up.

## 7. Postscript (same night): the three walls — final state of attempt 028

The §4a strip route and a difference-of-families repair were both built and both
refuted the same night (`tmp/att028b_strip_fast.py`, `tmp/att028c_wsplit.py`; RH ledger
028b/c). The dip is guarded by three independent, now-exact walls:

1. **Strip wall (termwise route).** Unconditional termwise validity needs
   `Re g(v+iw) ≥ 0` on a strip, and `Z(θ=0.5) = 1.3297 > 1.3275`: the toll exceeds the
   whole CGdL gain at half the box-hypothesis depth. Montgomery–Taylor's kernel itself
   violates strip positivity — the termwise route is dominated everywhere, even
   conditionally on the GS25 box.
2. **Autocorrelation wall (single-family inertia).** §2a: Frobenius kernels are
   `{w⋆w : w ≥ 0}`; they cannot dip; M–T is that class's exact optimum.
3. **Pair-index wall (two-family difference).** `M = A[√w₊] − A[√w₋]` realizes the dip
   kernel with Lemma 3.2 applicable, but pays the pair index twice (`8p` vs `4p`) —
   no bound survives on pair-heavy configurations — and the minimum-phase factor's
   trace toll alone is `4b̃ = 0.137` against a dip gain of `0.0063`.

**What stands:** the band-limited CGdL value `Z*(2) ≈ 1.3212` (validated LP), the walls
map, and the open problem: *a configuration-valid counting inequality consuming the pencil
data `(tr A₁, tr A₂, ‖A₁‖²_F, ‖A₂‖²_F, Re tr(A₁A₂†))` with pair charge `4p`.* The cross
term is the unique quadratic pair-functional whose kernel class dips. Its existence at the
CGdL-optimal kernel is worth exactly `0.6725 → 0.6788` unconditionally.

## 8. The S(t) route (attempt 029, Sam's steer): the walls bypassed, the target renamed

The 028-walls all guarded *sign-only* use of `(1,2]`. An unconditional upper bound
`∫₁^∞ F(α)/α² dα ≤ C` — "the row" — changes the game: the certificate keeps a
nonnegative window (`ĝ = w⋆w`, `w ≥ 0`, support up to the full band), evaluates its
out-of-band Frobenius mass from above by `t·C` (`t = sup_{(1,2]} ĝx²`, `F ≥ 0`), and runs
zeta23's inertia verbatim (tail estimate retuned to `D₀ = T^{3/4}`, inside their own
Remark 4.3 range). No dip, one form, pair charge `4p`.

**The reduction curve** (`tmp/att029_tailrow2.py`, self-consistent discretization):

| row bound C | ≥2 | 1.75 | 1.5 | 1.35 | 1.2 | 1.05 | 1 (PCC) |
|---|---|---|---|---|---|---|---|
| simple-on-line ≥ | 0.684 | 0.702 | 0.764 | 0.801 | 0.838 | 0.876 | 0.889 |

Physical floor: `F`'s diagonal forces the row `≥ N*/N`, so `C ≈ 1` is sharp and the
statement is self-referential in `N*` near the floor (bootstrap structure, unexplored).

**Why the row is the exact frontier (two closures):** (i) band-limited majorants cannot
upper-bound the tail — the support condition lives on the F-side weight, so band data +
positivity gives lower bounds only (the Goldston-1988/CCLM game, now understood as
one-directional); (ii) Goldston 1987 places the row at the constant level of `∫₀ᵀS²`,
which Selberg's unconditional error `O(T√loglog)` does not resolve. So:

> **the row ⟺ the unconditional constant-level second moment of S(t).**

That is a house-shaped problem: the compiled `StExplicitBridge` derives S-decompositions
with no RH anywhere (attempts 018/019 verified the accounting term by term, packets over
actual zeros, complex ordinates welcome), and attempt 012's machinery holds the band part
`V_line` exactly. An unconditional Goldston identity through the bridge — even with a
lossy explicit constant `C < 1.9` — moves the unconditional record via the curve above.

## 9. The Selberg-remainder chain (attempt 030): the row priced and measured

Dissecting Selberg's unconditional `√loglog` error shows it is pure Cauchy–Schwarz slack:
with `S = P + R` (band-limited mollified prime polynomial + remainder), the cross term is
band × remainder (no tail content) and is unconditionally *evaluable* by Landau–Gonek —
the very sums attempt 026 measured at median 1.0003. All `α > 1` content of `S` lives in
`R`. One-directionally:

> **row ≤ 2π² · c_R + o(1)**, where `∫₀ᵀ(S−P)² dt ≤ c_R·T` unconditionally,

with one obligation (Bessel-type embedding at complex ordinates; the off-line per-zero
S-profile carries exactly BGSTB's `x^{ρ+ρ̄′−1}` weights, so the pairing matches).

**Measured truth** (`tmp/att030_cR.py`, 22,491-zero census): `2π²c_R = 1.053` at
band-valid `x` — i.e. row ≈ 1 (PCC-consistent, matching 012's residual) + small
mollifier defects. The S₁-ladder is a understood dead end (integration damps the tail to
second order — tail-blind). The `x = T^θ` mollifier restriction is defused: the
unsubtracted `(θ,1]` band mass is `log(1/θ)`-worth, computable exactly.

**The project this prices:** an *explicit* unconditional `∫(S−P)² ≤ cT` sharp within
≈1.8× of truth gives `row ≤ 1.9` (record moves past 0.6725); within ≈1.4× gives
`row ≤ 1.5` ⟹ **0.764**. The prime side is constant-sharp (MV); the fight is the
zero-local term's second moment — whose per-line harmonic content is exactly what the
θ-tape law computes. This would be the first unconditional upper bound on any F-tail
integral, at any constant.

## 10. Attempt 031 + the explicit-c_R budget: the final architecture

**The reduction (final form, superseding §8's route):** the config-side LP with the row
as an admissibility constraint. `F = μ₂ + M` (spike = DC peak, mass 1, μ₂-independent;
diagonal = the constant floor μ₂; M = off-diagonal pair transform, positive-definite by
Bochner), band pinned to BGSTB. Then unconditionally-given-the-row, by integrality + LP
duality alone: **`∫₁^∞F/α²dα ≤ C ⟹ s₁/N ≥ 2 − μ₂max(C)`**, with the computed curve
(Goldston one-sided units; anchor C=∞ → M–T + 0.019 conservative slack):
C ≥ 1.9 inactive; 1.5 → 0.735; 1.33 → 0.795; 1.2 → 0.844; 1.05 (measured truth) → 0.902.

**The hypothesis map:** the row concerns the amplified F. S-instruments discharge the
damped row; the two coincide on box-configs (`e^{4A}`). The single residual enemy of full
unconditionality is the **middle band** (depths between A/log T and any fixed y₁), where
amplification `e^{4yαl}` outruns all known density theorems. Three appearances in one
session (strip toll, 030-correction, here) — one object.

**The explicit-c_R plan (task 5), corrected by a tautology check:** the cross term is
free (`∫PS = ∫P² + O(T^θ loglog)`, Landau–Gonek), so `∫R² = ∫S² − ∫P² + o(T)` exactly —
the chain is circular unless `∫S²` is bounded independently. Selberg's actual non-circular
input is the crude local count `N(t+1)−N(t) ≪ log t` (first moment only). Budget:
`2π²c_R ~ (local-count const/θ)² ≈ 1.8` at `θ = 1/3` with Bellotti–Wong's 0.10076 —
at the activation bar. All inputs explicit in print; θ-optimization open.
