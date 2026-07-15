# The value-registration transient, derived from the FE sheet

**Task.** Pin the on-lattice value-registration transient `R0(Y) - 1` (GRADE4
item 11) *by derivation*, not fitting: show it is the exact smoothed-AFE
truncation error of the windowed center read against the completed-L structure,
computable per object from the FE sheet `G(s)` with **zero fitted parameters**.

Files: `transient_form.py` (instrument), `transient_form_results.txt` (24-row
census output).

---

## 1. The derivation (one page of classical analysis)

The census reader is the canonical C∞ window sum (never-clip law)

```
    V_Y(1/2) = sum_{n>=1} lambda_n n^{-1/2} w(log n / log Y),   R0 = V_Y(1/2) / L(1/2),
```

with `w(u) = 1` for `u <= 1/2`, smoothly `-> 0` on `1/2 < u < 1`, `= 0` for `u >= 1`.

**Mellin step.** Let `wtilde(z) = int_0^inf w(log x / log Y) x^{z-1} dx` be the
window's Mellin transform. Integration by parts gives the clean closed form

```
    wtilde(z) = -psi(z)/z,    psi(z) = int_{1/2}^{1} w'(u) Y^{u z} du      (entire),
```

so `wtilde` has a **single simple pole at z = 0 with residue 1** (psi(0) = -1).
For `c > 1/2` the Dirichlet series converges and

```
    V_Y(1/2) = (1/2pi i) int_{(c)} wtilde(z) L(1/2 + z) dz.
```

**Shift + functional equation.** Move the contour left to `Re z = -c'` with
`c' in (1/2, 1)`. The only pole crossed is `z = 0` (residue `L(1/2)`; L is entire
for every census object — verified: no pole at s=1, coefficient means -> 0). On
`Re z = -c'` use `Lambda(s) = eps Lambda(1-s)`, `Lambda = G . L`:

```
    L(1/2+z) = eps . chi(z) . L(1/2-z),     chi(z) := G(1/2 - z) / G(1/2 + z).
```

`L(1/2-z)` now sits at `Re(1/2-z) = 1/2 + c' > 1`, so its Dirichlet series
converges and can be interchanged with the integral. The result is an **exact
identity** — the transient IS the mirror (dual) sum against the FE chi-factor:

```
    T(Y) := V_Y(1/2) - L(1/2)  =  eps * sum_{m>=1} lambda_m m^{-1/2} M_m(Y),      (T)

    M_m(Y) = (1/2pi i) int_{Re z = -c'} wtilde(z) [G(1/2-z)/G(1/2+z)] m^{z} dz.
```

Everything on the right is **on the sheet** (Q and the Gamma-shifts, through
chi) plus the SAME arithmetic coefficients. No L-value, no fit.

**Leading closed form.** With `chi(z) ~ Q_an^{-z}` (Q_an the analytic conductor),
the Perron step collapses `M_m` to a *complementary window*:

```
    M_m(Y)  ~  w( log(Q_an / m) / log Y ) - 1
```

i.e. `-1` for `m <~ Q_an/Y`, ramping to `0` at `m ~ Q_an/sqrt(Y)`. So

```
    T(Y)  ~  - eps * sum_{m <~ Q_an/sqrt(Y)} lambda_m m^{-1/2} [1 - w(log(Q_an/m)/log Y)],
```

**the smoothed dual partial sum up to m ~ Q_an/sqrt(Y).** Its shape (decay
exponent, oscillation phase) is fixed by the Gamma-shape of G — which is exactly
**why no single cross-object predictor survived the census CV**: different sheets
give different kernels, each deterministic per object.

**Numerics.** `M_m(Y)` is computed like `center_reading`'s H-grid: sample the
contour once, vectorize the m-dependence as an FFT on a log-grid + interpolation
(chi from `scipy.special.loggamma`, exact). Contour at `c' = 0.75` (avoids the
Gamma-poles that sit exactly at half-integer c'). Kernel verified three
independent ways: (i) c'-invariance over `c' in [0.55, 1.6]`; (ii) mpmath
quadrature at `m = 1,2,3,10`; (iii) direct high-resolution numpy integral vs the
interpolated grid at `m = 1..1500` (agree to 1e-7).

**Analytic-conductor caveat (a finding in itself).** The small-z digamma estimate
of Q_an collapses to O(1) for degree >= 4 (the Gamma-ratio's higher-order
structure dominates near its poles), so it is NOT the transient scale — the true
scale is ~ Q. The leading closed form must use Q, not the naive digamma value.

---

## 2. The 6-object result (24 census rows)

`resid = T_meas - T_pred`, `T_meas = V_Y - L`, both real, T_pred from the sheet.

| object | deg | Q | sheet G(s) = Q^{s/2} · | resid (all 4 Y) | verdict |
|---|---|---|---|---|---|
| L(11a1)   | 2 | 11      | Γ_C(s+½)                    | 1.6e-7          | EXACT |
| L(Sym²)   | 3 | 121     | Γ_C(s+1)Γ_R(s+1)            | ~2e-6           | EXACT |
| L(Sym³)   | 4 | 1331    | Γ_C(s+3/2)Γ_C(s+½)          | ~7e-6           | EXACT (sign changes captured) |
| L(Sym⁴)   | 5 | 14641   | Γ_C(s+2)Γ_C(s+1)Γ_R(s)      | ~1e-6           | EXACT (sign changes captured) |
| **RS4 = 11a1×37a1** | 4 | 165649 | Γ_C(s+1)Γ_R(s)Γ_R(s+1) | **+0.159,+0.148,+0.138,+0.132** | **extra term** |
| **deg6 = Sym²(11a1)×37a1** | 6 | 11⁴·37³ | Γ_C(s+3/2)Γ_C(s+½)² | **+0.034,+0.044,+0.049,+0.048** | **extra term** |

**Pre-registered criterion (sign + phase, zero params, at the census floor):**

- **MET for all four symmetric powers (16 rows).** T_pred reproduces T_meas to
  ~1e-6 — 3 to 4 orders of magnitude below the census row floors. This is a
  genuine, non-trivial validation: the Sym³ and Sym⁴ transients **change sign**
  across the Y-ladder (e.g. Sym⁴: -0.0056, -0.0031, +0.0029, -0.0014) and every
  sign and magnitude is predicted exactly from the sheet.

- **NOT met for the two Rankin–Selberg products.** For RS4 the leading mirror sum
  even has the wrong sign (T_pred = -0.065 vs T_meas = +0.094). The residual is
  Y-dependent (decays like ~Y^{-0.05}), so it is NOT a constant offset. The
  mirror-derivation-*implied* value `L = V_Y - T_pred` for RS4 is 5.18 -> 5.15,
  which disagrees with the Dokchitser-validated 5.0227652 — the mirror truncation
  error genuinely does not close the RS4 transient.

**The clean structural split.** The extra term appears for exactly the two genuine
automorphic PRODUCTS (both = something × 37a1, bad primes at two places) and NEVER
for a symmetric power (single object). It does not correlate with the Gamma-shape
(deg6 is all Γ_C; RS4 has two Γ_R; the clean Sym³ is all Γ_C, the clean Sym⁴ has a
Γ_R) — only with product structure. This is the discovered refinement of the
census's "no cross-object law": the symmetric powers obey the mirror law exactly;
the RS products carry an additional slowly-varying transient component the leading
smoothed-AFE mirror does not capture.

**deg6 value flag.** For deg6 the residual is near-constant ~+0.045, and the
mirror-implied `L = V_Y - T_pred` on the converged rows clusters at ~0.664 vs the
house value 0.61570486. Because the deg6 value was house-evaluator-only (Dokchitser
was dropped at degree 6, no independent oracle), this ~0.048 gap is ambiguous
between the RS-product extra term (as in RS4) and a house-evaluator error at
degree 6. **Worth an independent recheck of L(Sym²(11a1)×37a1, 1/2).**

---

## 3. Accelerated (sheet-subtracted) reader

Because T(Y) is computable from the sheet + the already-summed coefficients, the
honest reader `V_Y - T_pred` reads L directly (no L-value input):

- **Symmetric powers:** `V_Y - T_pred = L` to the bank floor at every Y —
  `|V_Y - T_pred - L|/L = 0.0000` vs raw `|V_Y - L|/L` up to ~1%. Clean, but the
  symmetric-power transients are already small, so the practical gain is modest.
- **deg6:** subtraction turns the 96%-off reading at Y=40000 (`|V-L|/L = 0.96`)
  into 5.5% (`0.055`) — a ~17x reduction — but a residual remains (the extra term).
- **RS4:** subtraction does NOT help (wrong-sign mirror) — the extra term dominates.

This does not beat the information bound (the mirror still runs to m ~ sqrt(Q_an)),
but where it closes (symmetric powers) it removes the slow-convergence overhead:
read L cleanly at the balance point instead of waiting for Y >> sqrt(Q).

---

## 3b. The two carrier forms: single rail vs conjugate pairing

Framed as the value-level sibling of the S(t)-compensation theorem
(`CarrierScaleCompensation.lean`, the theta-construction technique). There the zero
COUNT decomposes as

```
    N(t) = 1 + theta(t)/pi + S(t)     [DC residue + sheet clock + registration gap]
```

with `theta(t) = int_0^t Re(logDeriv Gamma_R(1/2+iu)) du` derived FROM THE SHEET (the
Gamma-factor) and `S(t)` the leftover compensation. The VALUE-level identity is the
exact sibling: `V_Y(1/2) = L(1/2) + [mirror term]` — the mirror term IS the
value-level `theta/pi + S`, the chart toll made explicit from the sheet. It has two
carrier reads (`transient_pairing.py`, `transient_pairing_results.txt`):

**FORM 1 — single rail `F_r`.** `F_r` is a half-lane object: lanes
`{(1+r)theta, (r-1)theta}`, the positive half of `Sym^{2r-1}`. Both lanes are
positive-frequency, so there is no conjugate to complete a Gamma-factor: `F_r` has NO
self functional equation (its dual is the OTHER rail `F_{-r}`) and NO archimedean
completion. => Estermann/Kurokawa **natural boundary at Re s = 1/2**: there is no value
to register and **the mirror term is absent**. The single-rail read DIVERGES; the sheet
bound (Rankin–Selberg `sum_{n<=N}|lam_n|^2 ~ cN` + Cauchy–Schwarz on the degree-2 lanes)
is `|read| <= N^{1/2}(log N)^{1/2}`. Measured (`F_2`, matches helix_pairing exactly):
reads 6.36, 9.99, 15.88, 25.06; growth exponent **+0.443** (sheet bound <= +0.5,
helix_pairing +0.427). The "single-rail transient" is a divergence — nothing to derive,
because there is no FE.

**FORM 2 — conjugate pairing `F_r (*) F_{-r}`.** The height-matched Hermitian pairing
`(F_r (*) F_{-r})[n] = sum_{d|n} lam_r[d] lam_{-r}[n/d]` symmetrizes the lanes
`{(1+r)th,(r-1)th} (x) {-(1+r)th,-(r-1)th} -> {+-(2r-1)th,...,+-th} = Sym^{2r-1}` (times a
bad-factor `C_r` at 11). This restores conjugate closure => the FULL `Sym^{2r-1}`
Gamma-factor `Gamma_C(s+(2r-1)/2)...Gamma_C(s+1/2)` => a genuine FE => **the mirror term
exists**. The paired read CONVERGES (r=2: reads 1.3593, 1.3659, 1.3689, 1.3682, matching
helix_pairing; growth exponent **+0.013**, helix_pairing +0.018), and its transient is
the mirror-term transient of the COMPLETED paired sheet.

Prediction test (r=2, `F_2(*)F_-2 = Sym3.C2`, sheet Q=11^3,
`Gamma_C(s+3/2)Gamma_C(s+1/2)`, eps=+1): the paired object's chi carries the extra
bad-factor FE reflection `C2(1/2+z)/C2(1/2-z)`. With that,

```
    Y        T_meas      T_pred(Sym3.C2)   resid
    4000    -0.00896     -0.00895         -8.9e-6
    16000   -0.00235     -0.00234         -8.6e-6
    64000   +0.00061     +0.00062         -8.7e-6
    250000  -0.00010     -0.00009         -8.5e-6
```

The residual is a CONSTANT ~8.6e-6 = the certified-value precision floor (L(Sym3) to 7
digits). The PURE Sym3 sheet (no C2 reflection) misses (-0.0016, +0.0003, -0.0014,
+0.0005) — so the bad-factor reflection is exactly the extra the pairing sheet carries,
and the completed sheet nails the pairing transient with ZERO fitted parameters.

**What the conjugate pairing buys, located analytically:** exactly the mirror term. The
single rail's mirror lives on the unreachable conjugate rail `F_{-r}`; the pairing brings
it internal by supplying the completed `Sym^{2r-1}` Gamma-factor (r copies of `Gamma_C`)
and the FE — absent from either half alone. The mirror term the pairing buys IS the
value-level compensation, the sibling of `theta(t)/pi + S(t)` supplying the count's
compensation in `CarrierScaleCompensation.lean`. (Second rung r=3:
`F_3(*)F_-3 = Sym4/zeta . C3` carries a zeta in the denominator — the zeta zeros enter as
poles of the paired sheet, a distinct analysis; noted, not the r=2 headline.)

---

## 4. Bottom line

The value-registration transient is, provably, the smoothed-AFE mirror truncation
error against the FE chi-factor — **confirmed at ~1e-6 with zero fitted parameters
for every symmetric-power object, including the sign and phase of its oscillation.**
The two Rankin–Selberg products carry an additional transient term the leading
mirror does not account for — a clean, falsifiable structural signature (products
vs symmetric powers) that itself explains why the census found no single
cross-object law, and which flags the (unvalidated) deg6 central value for recheck.
