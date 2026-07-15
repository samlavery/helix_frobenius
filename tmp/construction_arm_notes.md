# Construction arm of the Schoen recognition loop — the CYCLE side

Companion to `construction_arm.py` / `construction_arm_results.txt`, and to the
DETECTION arm `schoen_explicit.py` (item 39). Mystery-last (Recognition), the
one gate where truth is total: the explicit bielliptic Schoen fourfold, where
the Weil class is not just detected-as-frozen but is a **theorem-certified
algebraic cycle**. This file pins that cycle, translates it to carrier data, and
lands its integer fingerprints against the measured freeze. Method = the bf-loop
grade-2 template (`bf_loop_g2_notes.md` §5): construction arm delivers a
*carrier translation* + reachable numerics + a precisely named residual.

Everything here is unconditional: no RH/GRH, and — for the cyclic `m=3` case —
no Kleiman standard conjecture either (see §5, the register split).

---

## 1. The construction, pinned (exact citations)

**The object.** `E0 : y² + 2xy + y = x³` (conductor 19, non-CM, 3-torsion
`T=(0,0)`), `y` the "magic cube function" with `div_{E0}(y) = 3([T]−[O])`.
`C'` = bielliptic genus-3 double cover `w² = (x−1)(x+1)` over `E0`. `C` = the
**étale** `Z/3` cover `t³ = y` over `C'` (genus 7), deck `σ : t ↦ ζ₃ t`.
`B = Prym(C/C') = ker(Nm : J(C)→J(C'))₀`, an abelian fourfold with
`Q(ζ₃)=Q(√−3) ⊂ End⁰(B)` from `σ`, signature `(2,2)` — **Weil type**.

**The Weil-Hodge space.** `U_Weil := ⋀^{2g'−2}_{Q[G]_nt} H¹(B,Q) ⊂ H^{2g'−2}(B,Q)`,
of dimension `|G|−1 = 2`. For `m=3, g'=3` this is a 2-dimensional space of
`(2,2)` classes — the exotic Weil classes, NOT spanned by products of divisors.

**The explicit cycle (Patel–Zhang formulation of Schoen).** In the Cartesian
diagram (Patel–Zhang (1.0.1)), the degree-`(2g'−2)` Abel–Jacobi map
`AJ : Sym^{2g'−2}(C') → J(C')` is a `P^{g'−2}`-bundle away from one point, and
**its fibre over the canonical class `κ_{C'}` is the canonical linear system
`P^{g'−1} = |K_{C'}|`**. This `P^{g'−1}` is an explicit algebraic subvariety of
`Sym^{2g'−2}(C')`; **its class pulled back through the cover to `Sym^{2g'−2}(C)`
and projected to the `χ`-isotypic (Prym) block `B` is Schoen's cycle** —
codimension 2, generating `U_Weil`. For `m=3, g'=3`: `2g'−2 = 4`,
`P^{g'−1} = P²` = the canonical model of the (non-hyperelliptic) genus-3 curve
`C'` as a plane quartic, and `|K_{C'}|` = the `P²` of *lines* in that plane
(canonical divisors = line sections, 4 points = degree `2g'−2`).

**Citations (consumed, unconditional branch).**
- C. Schoen, *Hodge classes on self-products of a variety with an automorphism*,
  Compositio Math. 65 (1988) 3–32, **+ Addendum, Compositio 114 (1998) 329–336**
  (the fourfold). Constructs the cycle directly and computes its class ⇒
  **unconditional** algebraicity of `U_Weil` for cyclic étale covers.
- A. Patel, Y. Zhang, *Algebraicity of Hodge classes on some generalized Prym
  varieties*, arXiv:2506.13729 (2025). Reproves+generalizes via geometric class
  field theory; gives the clean `AJ`-fibre `= |K_{C'}|` description above. NOTE:
  their **general abelian-`G`** Theorem 1.2 invokes Kleiman's standard
  conjecture; the **cyclic `m=3`** case (ours) is credited to Schoen and is
  unconditional. We cite the unconditional branch only.
- B. van Geemen, *Weil classes and decomposable abelian fourfolds*,
  arXiv:2108.02087. The decomposable/imprimitive regime — the register of THIS
  member (see §3).
- E. Markman (2019–): Hodge conjecture for **all** Weil abelian fourfolds with
  CM in an imaginary quadratic field `≠ Q(i)` — an independent unconditional
  cover of our `Q(√−3)` fourfold.

---

## 2. The carrier translation (the arm's real deliverable)

Which carrier-side datum each ingredient of the cycle consumes, and where each
step is effective vs. existence-only. Pipeline: **carrier dossier IN → cycle
description OUT.**

| cycle ingredient | carrier datum it consumes | status |
|---|---|---|
| the cover `π:C→C'`, degree `m=3` | the **rail count**: `Q(ζ₃)` acts, `H¹(B)_C = W⊕W̄` | effective (read from `σ`-rails) |
| the deck action `σ` | the **rails themselves** — `W` = `σ=ζ₃` eigenspace = `Pi_W` block | effective (deg `Pi_W` = dim `W` = 4) |
| Prym block `B = ker(Nm)₀` | `L(B,T) = L(C,T)/L(C',T)`, the deg-8 Frobenius data | effective (fiber-product counter) |
| `Sym^{2g'−2}(C')`, `AJ`, `κ_{C'}` | the **base curve `C'`** (its canonical `P²` model) | angular: **not carried** (`L`-invisible); radial+Torelli: recoverable |
| `P^{g'−1}=|K_{C'}|` fibre class | the **theta/AJ / period side** of the carrier | needs `C'`; via the radial/period channel (§5) |
| `χ`-isotypic projection to `B` | the `Q(ζ₃)` **rail projectors** `⅓Σζ₃^{−k}σ^k` | effective (algebraic correspondences) |

**Operational reading.** The carrier presents `B` on its deck-rails: the order-3
automorphism `σ` (the cover's deck group) is the **cycle's algebraic engine**.
On the harmonic-Hodge frame the Weil class is a rational DC mode of the rail
pairing; the rail projectors `π_W, π_{W̄}` (`Q(ζ₃)`-combinations of the graphs
`Γ_{σ^k}`) are honest algebraic correspondences, and applying them isolates the
`∧⁴W ⊕ ∧⁴W̄` Weil line. **Effective steps:** everything driven by `σ` and the
Frobenius rails (the whole detection pipeline, plus the decomposable cycle of
§3). **Existence-only step:** the `AJ`-fibre `|K_{C'}|` for the *simple* member —
constructive *in principle* (Schoen writes it down given `C'`) but it consumes
the curve `C'`, which the carrier does not return (§4).

---

## 3. The explicit cycle for THIS member (decomposable — effective, closed)

`schoen_explicit.py` found this member **decomposable** (`B ~` a square; `Pi_W`
has real coefficients, `P_B = Pi_W²`). In that regime Schoen's heavy Sym+AJ
machinery is **not needed**: the Weil cycle is elementary.

- `σ ∈ End(B)` is an **order-3 fixed-point-free endomorphism** (deck group
  descends to the Prym). Its graph `Γ_σ ⊂ B×B` is an algebraic cycle, full stop.
- Since `B` is isogenous to a square, `σ` realizes `Q(ζ₃)` as an order-3 element
  of `M₂` over `End⁰` of the factor, mixing the two copies (char. poly `x²+x+1`).
- The rail projectors `π_W = ⅓(1 + ζ₃²σ + ζ₃σ²)`, `π_{W̄} = ⅓(1 + ζ₃σ + ζ₃²σ²)`
  are `Q(ζ₃)`-algebraic correspondences; applied to divisor products they cut
  `U_Weil` out **algebraically, unconditionally** (van Geemen 2108.02087 — the
  decomposable/imprimitive Weil classes are algebraic "for free").
- `P_B` factorisation read at each prime (from `construction_arm.py`): two
  elliptic `L`-factors, each **squared** — e.g. `p=7`: `(7T²−4T+1)²(7T²+3T+1)²`;
  at `p=43` the two factors fuse into an irreducible quartic (an abelian
  surface `A` with the `ζ₃` acting), squared. The square structure = the
  imprimitivity = why the cycle is elementary.

So for the concrete bielliptic member the construction arm is **CLOSED and
effective**: cycle = `{Γ_σ, divisor products, rail projectors}`, all readable
from the L-data. Schoen/Markman are the cited *theorems*; the cycle is elementary
enough to exhibit by hand here.

---

## 4. Recognition certificates — the numerics (`construction_arm.py`)

Eight integer landings, each tied to a named construction ingredient, checked
against the point-counted `B` at `p ∈ {7,31,37,43}`, `k=1..4` (fiber-product
counter reused from `schoen_explicit.py`, oracle-free).

| # | landing | ingredient | result |
|---|---|---|---|
| L1 | `2g(C)−2 = m(2g'−2)`: `12 = 12` | étale Riemann–Hurwitz | LAND |
| L2 | `g(C) = g'+(m−1)(g'−1)`: `7 = 3+4` | Chevalley–Weil genus | LAND |
| L3 | `dim B = (m−1)(g'−1) = 4` | Prym / fourfold | LAND |
| L4 | `dim W^{1,0} = g'−1 = 2` each rail ⇒ sig `(2,2)` | Chevalley–Weil | LAND |
| L5 | `dim U_Weil = |G|−1 = 2` | Weil space | = measured **collective 2** |
| L6 | `C(4,2) = 6` | divisor baseline | = measured **diagonal 6** |
| L7 | `tr(σ|H¹B) = −4` (two routes agree) | **deck engine** | LAND |
| L8 | **`det(Frob|W) = p²`** at every prime | **Schoen alg ⇒ Tate** | LAND |

- **L7 (the deck engine).** Two independent routes to `tr(σ|H¹B)`: (a)
  Chevalley–Weil, each rail char has multiplicity `2(g'−1)=4` on `H¹(B)`, so
  `tr = 4ζ₃+4ζ₃² = −4`; (b) étale-Lefschetz, `σ` acts *freely* (`#Fix σ = 0`)
  ⇒ `L(σ)=0` ⇒ `tr(σ|H¹C)=2` ⇒ `tr(σ|H¹B)=2−2g'=−4`. They agree — and the
  MEASURED cross-check is `deg Pi_W = dim W = 4`. Falsifiable: a ramified cover
  would give `#Fix σ > 0` and a different trace.
- **L8 (the recognition arc).** Schoen: `U_Weil` is a codim-2 **algebraic**
  cycle ⇒ its class is **Tate** ⇒ Frobenius acts on the Weil line `∧⁴W` by
  `p^{dim W/2} = p²`. So `det(Frob|W) = ∏β_k` must equal `p²` **exactly**.
  MEASURED: `det(Frob|W) = [49, 961, 1369, 1849] = [7², 31², 37², 43²]` — the
  literature cycle and the point-counted freeze **meet on an exact integer** at
  every prime. The exterior reading agrees: `∧²W ⊗ ∧²W̄` = `6` diagonal
  (`=C(4,2)`) + `2` collective (`= dim U_Weil = |G|−1`) at every prime.

This is the genuine arc closed: the theorem-certified algebraic cycle predicts a
Tate eigenvalue, and the unconditional point count confirms it exactly. The
"decomposable" register is also confirmed numerically (real rail at every
prime; the pre-registered *simple-member tell* — complex `Z[ζ₃]` rail — is
ABSENT, as expected for this member).

---

## 5. The generalization memo — is construction ∘ inversion well-defined?

The inversion arm's recovered-data boundary (**confirmed by `carrier-inversion`**,
2026-07-13): its instrument reads only the **angular + arithmetic** side of the
carrier — everything it outputs is a datum of the 1D projection / `L`-function.
Recovered: (a) the **Prym isogeny class** (`L(B,T)` per-prime Frobenius char-polys
⇒ by Faltings the `K`-isogeny class of `B` and no more; plus the finite invariants
signature `(2,2)`, decomposability via rail reality, bad-prime set); (b) the
**`D`-mod-cubes freeze label** (`χ₃(disc f·disc g²)` — which for THIS Schoen member
is the *trivial* class, freeze order uniformly 1, so it carries no distinguishing
information here, only on non-trivial-disc members); (c) the **`Z/3` deck rails**
natively (the `Z[ζ₃]` rail lattice, `σ=ζ₃` labeling, `K=Q(√−3)`). NOT recovered:
(d) the curve `C'` or the cover — Faltings gives isogeny, not isomorphism, so the
isomorphism class of `C'` is **theorem-absent from the `L`-function**. Does
Schoen's construction need more than (a)–(c)?

**Two regimes, one sharp gap.**

- **Decomposable / imprimitive gate (where truth is total — THIS member).**
  Construction ∘ inversion is **WELL-DEFINED**. The cycle is `{Γ_σ, divisor
  products, rail projectors}`, and *all* of these are readable from the isogeny
  class + rails: the factors come from `P_B`'s factorisation, the deck
  endomorphism `σ` is the `ζ₃`-rail structure itself. The carrier's recognition
  data **suffices to rebuild the cycle**. This is why the recognition gate is
  total here: detection (freeze) AND construction (cycle) both close on carrier
  data alone.

- **Simple gate (the frontier member, not yet built).** Construction ∘ inversion
  is **UNDER-DETERMINED**. Schoen's Sym`^{2g'−2}(C')`+AJ cycle consumes the
  **curve `C'` itself** — its canonical `P²` model, the `|K_{C'}|` of lines.
  The carrier returns only the Prym *isogeny class*, which does **not** pin `C'`:
  the Prym/cover moduli fibre over a fixed isogeny class is positive-dimensional
  (many genus-3 covers share a Prym isogeny class — Prym-Torelli is not
  injective at this genus and, more to the point, the L-data see only the
  isogeny class, a coarser invariant than the isomorphism class of `C'`).

**The named residual core (the deliverable that matters most).** The last
mystery's construction gap is *exactly* the gap between **"the Prym isogeny
class"** (what the carrier's angular reading provides) and **"the curve `C'`"**
(what Schoen's simple-member Sym+AJ cycle inputs). Crucially, these coincide with
the regime boundary: in the **decomposable** regime the cycle is
isogeny-class-reconstructible (no `C'` needed), so the gap is empty and the loop
closes; in the **simple** regime the cycle needs curve-level data, so the gap is
exactly one curve `C'` wide. Recognition (certifying algebraic-and-Tate — L8) is
well-defined on carrier data in **both** regimes; only *writing the simple cycle*
needs `C'`.

**The gap IS the carrier's angular/radial split — and it is bridgeable, not
fundamental** (`carrier-inversion`'s closure route, consistent with the
K3-radial finding, weil-campaign-state items 42–43). The missing `C'`-coordinate
is precisely the datum the 1D projection drops: `C'` is `L`-invisible because the
`L`-function only sees the isogeny class (angular data). But the 3D **radial /
period** channel *retains* exactly this coordinate, and for a non-hyperelliptic
genus-3 curve **Torelli** is effective — the ppav `Jac(C')` together with its
principal polarization determines `C'` up to isomorphism. So the construction gap
is not an obstruction but a *named extension*:

> **cycle = Schoen ∘ Torelli ∘ radial-reading** — recover `Jac(C')` + polarization
> from the carrier's radial/period channel (NOT the angular `carrier_inversion.py`,
> which is purely angular), run effective genus-3 Torelli to pin `C'`, then apply
> Schoen's Sym`^{2g'−2}(C')`+AJ construction.

**Exactness of the Torelli step (`carrier-inversion`, refinement).** For genus 3
the effective reconstruction is clean *precisely on the non-hyperelliptic
(plane-quartic) locus*: the canonical model is the quartic, directly recoverable
from the polarized period matrix via theta-nulls / bitangents. The
**hyperelliptic locus is the Torelli ramification** and needs a separate
reconstruction. Consequence, and a design constraint on the frontier object: the
**simple-frontier member must be non-hyperelliptic by design** — which is exactly
item 39's already-named simple target (an involution-free genus-3 curve / plane
quartic with a rational cubic tritangent giving `div(G/L³)=3D`). So the
radial+Torelli route and the item-39 simple-member target are the same object
seen from the two arms: build it non-hyperelliptic and Torelli pins it cleanly.

The residual is thus sharpened from "the curve `C'` is not a carrier invariant"
to the precise statement: **`C'` is not an *angular* carrier invariant (absent
from the `L`-function), but IS a radial/period one — recoverable via the
period channel + genus-3 Torelli.** The angular inversion instrument delivers the
isogeny-class-and-coarser layer where the loop already closes (decomposable
gate); the `C'`-pinning layer for the simple gate is the radial+Torelli
extension, still to build. That extension is the precise construction-side core
of the last mystery.

This is the honest partial with the failure point named (the bf-loop precedent):
the arm **closes** at the decomposable truth-gate (all 8 landings), and names its
single residual — the radial/Torelli recovery of `C'` for the simple gate — as a
bridgeable, precisely-located extension, not a wall.

---

## 6. Register (consumed / claimed / split)

- **Consumed theorems (cited, not reproven):** Schoen 1988+1998 (unconditional
  cyclic-cover algebraicity — the L8 input); Chevalley–Weil (genus/signature
  L2/L4/L7); Riemann–Hurwitz (L1); van Geemen 2108.02087 (decomposable cycle,
  §3); Markman (independent `Q(√−3)` cover); Patel–Zhang 2506.13729 (the
  `AJ`-fibre description; general-`G` branch is Kleiman-conditional and NOT
  invoked).
- **Claimed:** exactly the 8 integer landings and the decomposable cycle
  exhibit — no more. The freeze data is unconditional point counts; the
  algebraicity is a cited theorem; the recognition arc is their exact meeting on
  `det(Frob|W)=p²`.
- **Effective vs. existence.** Effective: L1–L8, the decomposable graph cycle,
  the whole rail pipeline — all on the carrier's *angular* data alone.
  Existence-only (not carried here): Schoen's simple-member
  Sym`^{2g'−2}(C')`+AJ cycle (needs `C'`); Abel–Jacobi and the `χ`-isotypic
  projection in the general formulation. The `AJ`-fibre `=|K_{C'}|` is
  constructive given `C'`, and `C'` is recoverable — not from the `L`-function
  (angular; Faltings ⇒ isogeny only) but from the carrier's **radial/period
  channel via effective genus-3 Torelli** (`carrier-inversion`'s confirmed
  route). So the simple-member cycle is "existence-only" *on the angular
  instrument*, "effective in principle" *on the radial extension* — that split
  is §5's sharpened residual core.
- **Boundary confirmation.** `carrier-inversion` (2026-07-13) confirmed the
  recovered-data boundary used here: angular instrument returns isogeny class +
  `D`-mod-cubes + `Z/3` rails; `C'` is `L`-invisible; the radial+Torelli
  extension is the named (unbuilt) route to it.
