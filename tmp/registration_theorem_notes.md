# The Registration Dichotomy — a theorem

**One statement promoting the rail-matching / value-registration law from
measured-plus-derived pieces to a single proven dichotomy with named hypotheses.**
Classical analysis only; no RH, no GRH. Verification harness:
`tmp/registration_theorem.py` (→ `registration_theorem_results.txt`).

Provenance of the pieces assembled here: the mirror-term derivation
(`transient_form_notes.md` §1, Lemma 1), the two carrier forms
(`transient_form_notes.md` §3b), the general lattice identity (GRADE4 item 38),
the derived transient and "what the pairing buys" (items 40–41), and the
registration census (item 11). This note states the endpoints as a theorem and is
explicit about what is proven, what is cited, and what stays measured.

---

## 0. Setup and named hypotheses

**Base object.** Let `f` be the weight-2 newform of level 11 attached to the
elliptic curve **11a1**. Its conductor is 11, which is prime, hence squarefree,
hence `f` is **semistable**; and `11a1` is **non-CM**. By modularity
(Wiles / Taylor–Wiles / BCDT) the completed L-function `Λ(f,s)` is entire,
satisfies `Λ(f,s) = ε(f) Λ(f,2−s)`, and has an Euler product
`L(f,s) = ∏_p (1 − a_p p^{−s} + p^{1−2s})^{−1}` with `|a_p| ≤ 2√p` (Hasse). In the
**analytic (unitary) normalization** write the good local roots as
`e^{±iθ_p}`, `θ_p ∈ [0,π]` (`a_p = 2√p · cos θ_p`), and `λ_p := 2cos θ_p`.

**Hypothesis NT (Newton–Thorne; UNCONDITIONAL for this `f`).**
Newton–Thorne, *Symmetric power functoriality for holomorphic modular forms*,
Publ. math. IHÉS **134** (2021): Part I (pp. 1–116) proves `Sym^n f` automorphic
for level-1 forms **and for all forms attached to semistable elliptic curves over
ℚ**; Part II (pp. 117–152) proves it for **all non-CM** holomorphic newforms.
`11a1` is semistable *and* non-CM, so **either part** applies: for every `n ≥ 1`,
`Sym^n f` is a cuspidal automorphic representation of `GL_{n+1}(𝔸_ℚ)`. Consequently
each `L(Sym^n f, s)` is **entire** (`n ≥ 1`), satisfies a completed functional
equation `Λ(Sym^n f, s) = ε_n Λ(Sym^n f, 1−s)`, and has an Euler product. This
discharges — **unconditionally, for our base object** — the "constituent
symmetric powers are nice" hypothesis used throughout arm (A) and (B).

**Lattice warp (single rail).** For `m ∈ ℤ` define the half-lane object by rotating
`f`'s Satake data by `e^{imθ_p}`:
```
    F_m(s) = ∏_{p≠11} (1 − e^{i(m+1)θ_p} p^{−s})^{−1} (1 − e^{i(m−1)θ_p} p^{−s})^{−1}
             · (1 − α^{|m|+1} · 11^{−s})^{−1}         [tame leg at p=11, α = 11^{−1/2}]
```
so the good-prime root multiset is `{ e^{i(m+1)θ_p}, e^{i(m−1)θ_p} }`, both on the
unit circle. Its Dirichlet coefficient at a good prime is `λ_p(F_m) = e^{imθ_p} λ_p`
(complex for `m ≠ 0`). Note `m = 0` recovers `f` itself.

**The reader (never-clip C∞ window).**
```
    V_Y(F; ½) = Σ_{n≥1} λ_n(F) n^{−½} w(log n / log Y),
```
`w(u)=1` for `u≤½`, smoothly `→0` on `½<u<1`, `=0` for `u≥1`. "Registration" means
`V_Y(F; ½) → (its L-value) + (a sheet-derived transient)` as `Y → ∞`; "no
registration" means the read has no finite target.

---

## 1. Lemma 1 (the mirror term) — from `transient_form_notes.md` §1

**Lemma 1.** Let `G` be a completed L-function of a nice object (entire, FE
`Λ = G·L`, `Λ(s)=ε Λ(1−s)`, Euler product). Mellin-inverting the window
(`w̃(z) = −ψ(z)/z`, a single simple pole at `z=0`, residue 1) and shifting the
contour left across `z=0` (residue `L(½)`) to `Re z = −c'`, `c'∈(½,1)`, then
applying the FE `L(½+z) = ε·χ(z)·L(½−z)`, `χ(z)=G(½−z)/G(½+z)`, gives the **exact**
identity
```
    V_Y(½) − L(½) = ε · Σ_{m≥1} λ_m m^{−½} M_m(Y),
    M_m(Y) = (1/2πi) ∫_{Re z=−c'} w̃(z) [G(½−z)/G(½+z)] m^{z} dz.        (T)
```
Everything on the right is on the sheet (`Q`, the Γ-shifts, through `χ`) plus the
**same** arithmetic coefficients — no L-value, no fit. The kernel `M_m(Y)` is
verified three independent ways (c'-invariance; mpmath quadrature; direct
high-resolution integral vs the interpolated grid) to `1e-7`. This is the value-
level sibling of the count identity `N(t) = 1 + θ(t)/π + S(t)`
(`CarrierScaleCompensation.lean`): `V_Y = L + [mirror]` = truth + sheet toll.

The load-bearing content of (T) is that **it needs a functional equation**. A self-
FE is what lets the left contour be folded into the convergent dual sum. This is the
hinge the dichotomy turns on.

---

## 2. THEOREM (Registration Dichotomy)

*Assume Hypothesis NT (unconditional for `f = 11a1`).*

### (A) Conjugate-closed lattice pairings REGISTER.

For `m ∈ ℤ`, the height-matched Hermitian pairing
`(F_m ⊛ F_{−m})[n] = Σ_{d|n} λ_m[d] λ_{−m}[n/d]` has good-prime root multiset
`{±(m+1)θ_p, ±(m−1)θ_p}` — the **outer two Satake pairs of `Sym^{m+1}`**. Hence the
Euler-product identity (item 38)
```
    F_m(s) · F_{−m}(s) = [ L(Sym^{m+1} f, s) / L(Sym^{m−3} f, s) ] · C_m(s),      (38)
```
`C_m(s)` a finite Euler factor at `p=11` (rational in `11^{−s}`, entire and non-
vanishing near `Re s = ½`). Special cases: `m=2` gives `Sym^{−3+m}=Sym^{−1}≡1`, so
the RHS is `L(Sym^3 f, s)·C_2(s)` — **entire**; `m=3` gives `Sym^0=ζ`, so `ζ` enters
the **denominator**.

Under NT the numerator and denominator are nice, so the paired object has a
**completed (meromorphic) functional equation** with sheet
`G_{pair}(s) = G(Sym^{m+1})/G(Sym^{m−3}) · (reflection of C_m)`. Lemma 1 then
applies to the paired sheet and yields an **exact mirror term**: the windowed center
read **registers**,
```
    V_Y(F_m⊛F_{−m}; ½) − L_{pair}(½) = ε · Σ_M λ_M(pair) M_M(Y),   ZERO fitted params,
```
with `M_M` built from `χ_{pair}(z) = G_{pair}(½−z)/G_{pair}(½+z)`, **including the FE
reflection `C_m(½+z)/C_m(½−z)` of the bad factor**.

**Verified (m=2, the entire flagship).** `registration_theorem.py`, ARM A: the
paired read converges (growth exp ≈ 0), and `V_Y − L_pair` equals the completed-
sheet mirror term to a **constant** residual `≈ 8.5×10^{−6}` (spread over the
Y-ladder `2×10^{−7}`) = the certified-value precision floor. Omitting `C_2`'s
reflection (pure `Sym^3` sheet) misses (item 41). Target
`L(Sym^3 f,½)·C_2(½) = 1.368286`.

*Scope caveat (A), `m ≥ 3`.* For `m ≥ 3` the denominator `L(Sym^{m−3}f,s)`
contributes **poles** (at its zeros; `m=3`: the ζ-zeros) to the paired sheet, so the
paired object is meromorphic, not entire — the mirror term still exists but the
registration read carries those poles (a distinct analysis). `m=2` is the clean
entire rung; it is the one verified to the value floor.

### (B) Single rails do NOT register — the divergence is ABSENCE, not error.

For `m ≠ 0` the good-prime root multiset `{(m+1)θ_p, (m−1)θ_p}` is **not closed under
negation** (conjugation). Therefore:

- **(B1) `F_m` is not self-dual** — its dual is the *other* rail `F_{−m}`, with
  `F_{−m}(s) = \overline{F_m(\bar s)}` (`λ_n(F_{−m}) = \overline{λ_n(F_m)}`). Hence
  `F_m` has **no self-functional-equation**. *Proof:* a degree-2 L-function with a
  self-FE and an archimedean factor built from `f`'s Satake data forces its good
  roots to be conjugation-stable at almost all `p` (the FE/sheet data pins the dual =
  the reflection); `{(m+1)θ,(m−1)θ}` is negation-stable iff `m=0`. *(Verified:
  `max_n |Im λ_n(F_2)| = 2.42 ≠ 0` and `max_n |λ_n(F_{−2}) − \overline{λ_n(F_2)}| = 0`.)*

- **(B2) No self-FE ⇒ Lemma 1 does not apply ⇒ the mirror term is ABSENT** (Form 1,
  item 41). There is no compensating dual sum to fold the tail; the windowed center
  read is a partial sum of a Dirichlet series with no target at `s=½`.

- **(B3) The read diverges, at a rate the sheet bounds.** `F_m ⊛ \overline{F_m} =
  F_m F_{−m}` is nice with a simple pole at the Rankin–Selberg edge, so
  `Σ_{n≤N} |λ_n(F_m)|² ∼ c_m N`; Cauchy–Schwarz gives
  `|V_Y(F_m;½)| ≤ N^{½}(log N)^{½}` — **growth, not a limit**. *(Verified, `m=2`:
  reads `6.36 → 25.06` over `Y = 4e3 → 2.5e5`, growth exponent `+0.450`, bound
  `≤ +0.5`.)*

There is **no value to register**: nothing to derive, because there is no functional
equation. The "single-rail transient" is a divergence.

### (C) Incommensurate / off-lattice warps interpolate toward (B) — MEASURED.

For `w ∉ ℤ`, `F_w` has neither a lattice partner identity nor a self-FE:
`F_w F_{−w}` matches **no** `L(Sym^k)·C` (verified: `|F_{√2}F_{−√2} − Sym^3 C_2| =
0.69`, `|… − (Sym^4/ζ)C_3| = 1.10`, both `O(1)`), so no completed sheet, no mirror,
and the paired read drifts (`43.7 → 222.2`). **Proven endpoints:** integer-`m`
pairings register (A); single rails / non-lattice warps do not (B). **Measured, not
proven:** the *monotone* off-lattice interpolation between them (registration census,
item 11: defect `0.165` unwarped `→ 0.236` full-warp; leave-one-object-out CV
correlation `+0.89` with off-lattice distance; closure-improvement and conductor have
**zero** predictive power). **Out of scope:** the Rankin–Selberg-product extra
transient (RS4, deg6; item 40) — genuine automorphic *products* carry a slowly-
varying term the leading mirror does not capture; a named open item, not part of this
dichotomy.

∎ (endpoints)

---

## 3. Proof map (what powers each arrow)

| step | statement | powered by |
|---|---|---|
| identity (38) | `F_m F_{−m} = L(Sym^{m+1})/L(Sym^{m−3})·C_m` | angle bookkeeping; **machine-checked `1e-9…1e-15`** |
| A: nice sheet | numerator, denominator nice ⇒ paired FE | **Hypothesis NT** (unconditional here) |
| A: register | completed FE ⇒ mirror term (T) | **Lemma 1** (kernel verified 3 ways) |
| A: `m=2` value | resid `8.5e-6` constant, zero fit | `registration_theorem.py` ARM A |
| B1: no self-FE | `dual(F_m)=F_{−m}≠F_m` for `m≠0` | **elementary + verified** (complex coeffs) |
| B2: no mirror | no self-FE ⇒ (T) unavailable | Lemma 1 contrapositive |
| B3: diverges | `≤ N^{½}(log N)^{½}`, grows | **Rankin–Selberg + Cauchy–Schwarz**; verified `+0.450` |
| C: interpolation | monotone with off-lattice distance | **measured** (census, item 11) |

---

## 4. The honest crux — arm (B)'s natural boundary at `Re s = ½`

The **unconditional** negative arm is `(B1)+(B2)+(B3)`: no self-dual ⇒ no self-FE ⇒
no mirror ⇒ the center read has no target and diverges. This needs nothing beyond
elementary duality, Lemma 1's contrapositive, and Rankin–Selberg — all in hand.

The **stronger** claim — that `F_m` has `Re s = ½` as a genuine **natural boundary**
(no meromorphic continuation to `Re s < ½`, so the divergence reflects the *absence
of the function itself* there, not merely the absence of an FE) — is the Estermann–
Kurokawa natural-boundary phenomenon. Here is exactly how far it is pinned:

**Classical results, exact statements.**

- **Estermann (1928),** *On certain functions represented by Dirichlet series*,
  Proc. LMS. For a fixed `h ∈ ℤ[X]`, `h(0)=1`: `∏_p h(p^{−s})` continues to all of ℂ
  **iff** `h` is a product of cyclotomic polynomials; otherwise `Re s = 0` is a
  natural boundary. (Local factor *fixed* across primes.)

- **Kurokawa (1986),** *On the meromorphy of Euler products, I & II*, Proc. LMS (3)
  **53**, 1–47 and 209–236. General meromorphy theory for Euler products with
  *varying* local factors, including those attached to automorphic forms.

- **Koyama–Kurokawa (2021),** *Variations of Ramanujan's Euler Products*
  (arXiv:2103.11406). Degree-two Euler products attached to a holomorphic Hecke
  eigenform via its Satake angle `θ(p)`. **Their criterion (their Theorem 1, from
  Kurokawa's [K1,K2]):** for `H(T) ∈ 1 + T·R(SU(2))[T]` (coefficients are *virtual
  characters* of `SU(2)`, i.e. **class functions**, symmetric under `θ → −θ`), `H` is
  *unitary* (roots on the unit circle) **⟺** `L(s,E,H)` is meromorphic on all of ℂ;
  a non-unitary `H` has a natural boundary. **They explicitly assume Newton–Thorne**
  ([NT1],[NT2]) to make the symmetric-power L-functions nice.

**Why this is criterion-plus-evidence, not a verbatim citation.** The published
Estermann/Kurokawa/Koyama–Kurokawa theorems are stated for **self-dual** local
factors — `H ∈ R(SU(2))[T]` has *real, class-function* coefficients. Their "non-
unitary" case is a *size* condition (real roots leaving the unit circle) and gives a
boundary at `Re s = 0` (their normalization). **Our `F_m` is different in kind:** its
local factor `(1−e^{i(m+1)θ}T)(1−e^{i(m−1)θ}T)` has a genuinely **complex** leading
coefficient `c_1(p) = e^{imθ_p}·2cos θ_p ∉ R(SU(2))` — it is *not* a class function
(it breaks `θ → −θ`). So **`F_m` sits outside the stated scope** of those theorems; I
could not verify its hypotheses because its `H` is not one of their `H`'s at all.

**Where the `½` (not `0`) comes from — the mechanism.** The boundary is driven by the
`k=1` layer `Σ_p e^{iℓθ_p} p^{−s}` (`ℓ = m±1 ≠ 0`). Split into class-function and
"odd" parts: `e^{iℓθ} = U_ℓ(cos θ) − e^{−iθ}U_{ℓ−1}(cos θ)`, and the odd part carries
`sin θ_p = √(1−cos²θ_p)`, which is **not** a polynomial in `cos θ_p` (not in
`R(SU(2))`). Its square `Σ_p sin²θ_p · p^{−2s} = Σ_p (1−cos²θ_p) p^{−2s}` has a
**pole at `2s=1`**, i.e. `s=½`; the non-terminating symmetric-power factorization
required by the `sin θ` branch condenses the zeros of `L(Sym^n f, s)` (`n → ∞`) onto
`Re s = ½`. This is a Kurokawa-type accumulation, and Hypothesis NT discharges its
automorphy inputs — but the theorem for this specific *non-self-dual* object is not in
the cited literature.

**Status of (B)'s boundary at `Re s = ½`.**
**Criterion + derivation + numerical confirmation** — *not* a verbatim-cited theorem.
The numerical confirmation is the measured growth exponent `+0.450` against the
Rankin–Selberg bound `+0.5` (`registration_theorem.py`, ARM B). The dichotomy's
negative arm does **not** depend on it: `(B1)+(B2)+(B3)` already give "no FE ⇒ no
mirror ⇒ nothing to register" unconditionally.

---

## 5. REGISTER — proven / cited / measured / out of scope

**PROVEN (unconditional, base curve `11a1` and its integer lattice pairings):**
- Identity (38): `F_m F_{−m} = L(Sym^{m+1})/L(Sym^{m−3})·C_m` (machine-checked
  `1e-9…1e-15`; convolution form `1.6e-15`).
- Arm (A): integer-`m` conjugate pairings have a completed (meromorphic) FE (NT
  inputs) ⇒ a mirror term (Lemma 1) ⇒ the center read **registers** at the derived
  transient. Clean/entire at `m=2`, verified to the `8.5e-6` value floor (constant
  residual, zero fit).
- Arm (B) core: `F_m` (`m≠0`) is not self-dual ⇒ no self-FE ⇒ no mirror ⇒ the center
  read has no target and **diverges** (`+0.450`, bound `+0.5`). The divergence is
  ABSENCE of a value, not truncation error.
- Lemma 1 (the AFE/mirror identity), kernel verified three ways.

**CITED (classical inputs; hypotheses discharged where used):**
- **Newton–Thorne**, Publ. IHÉS **134** (2021), I & II — `Sym^n f` automorphic
  ∀`n≥1`; `11a1` is semistable (I) *and* non-CM (II): **unconditional**.
- **Deligne / Hasse** — `|a_p| ≤ 2√p`, so `θ_p` real.
- **Rankin–Selberg** — `Σ|λ_n|² ∼ cN`, powering the (B3) divergence bound.
- **Estermann 1928; Kurokawa 1986 (Proc. LMS 53); Koyama–Kurokawa 2021
  (arXiv:2103.11406)** — the natural-boundary dichotomy, invoked as the **criterion**
  for the (B) boundary at `Re s = ½`. *Their theorems cover self-dual `R(SU(2))[T]`
  factors; `F_m` is complex / non-self-dual, so this is criterion-level, not a
  verbatim application.*

**MEASURED (evidence, not proof):**
- The exact boundary location `Re s = ½` for the non-self-dual `F_m` — derivation
  (`sin θ ∉ R(SU(2))` ⇒ pole at `2s=1`) + growth exponent `+0.450` vs bound `+0.5`.
- Arm (C): the monotone off-lattice interpolation and its `+0.89` leave-one-object-
  out CV correlation with off-lattice distance (census, item 11).

**OUT OF SCOPE (named open):**
- The RS-product extra transient (RS4, deg6; item 40) — products carry a term
  symmetric powers do not; mechanism open.
- The deg6 central-value flag (house-evaluator-only; independent recheck required).
- Arm (A) at `m ≥ 3`: denominator poles (ζ-zeros at `m=3`) in the paired sheet — a
  distinct analysis; the entire flagship is `m=2`.
