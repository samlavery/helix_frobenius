# The carrier inversion arm — well-posedness

Companion to `tmp/carrier_inversion.py` (blind protocol; truth consulted only at
grading) and its output `tmp/carrier_inversion_results.txt`. This is the alignment
step of the collective recognition loop: the demonstration that the carrier's
per-prime readings **determine** the cover's arithmetic data, and the exact
statement of how much they determine.

Object: `B = Prym` of the cyclic cubic cover `C : y^3 = f(x) g(x)^2`
(`f,g` monic coprime squarefree, `3 ∤ deg fg^2`); a `(2,2)` [`g_W=4`] or `(3,3)`
[`g_W=6`] abelian variety of Weil type over `K = Q(√-3)`, carried on the `ζ_3`
deck-rails `W ⊕ W̄`. The analytic bridge inverted is the **freeze-order mechanism
theorem** (`freeze_mechanism_notes.md`, GRADE4 item 37):

```
det(Frob_p | V_ζ) = (-1)^{δ_p} · p^{g_W/2} · χ_3(D),     D = disc(f)·disc(g)^2,
r_p := det/((-1)^{δ_p} p^{g_W/2}) = χ_3,p(D),            δ_p = 0 at rational-branch good p.
```

---

## What the carrier reading is (two layers)

1. **The freeze stream** `{r_p = χ_3,p(D)}_p` — a **single cubic Dirichlet character**
   of the discriminant datum `D = disc(f)·disc(g)^2`. Read as the freeze scalar
   `wedge^{g_W} W / p^{g_W/2}`, a `μ_3` element (index `e_p ∈ {0,1,2}`).
2. **The angle stream** `{ char.poly(Frob_p | W) }_p` — the full `W`-rail L-polynomial
   at every good prime, i.e. **the L-function `L(B,s)`** (equivalently the collection
   of Frobenius characteristic polynomials).

---

## The determination ladder (three tiers, sharp)

**Tier 1 — freeze stream ⟹ `D mod cubes`, and no more of `(f,g)`.**
Because `χ_3` is a cubic character, `r_p` depends only on the class of `D` in
`Q*/(Q*)^3`. Recovered blind (Part 1) by solving, over `F_3`, the Chebotarev system
```
e_p  ≡  Σ_{ℓ ∈ S} a_ℓ · c_p(ℓ)   (mod 3),     a_ℓ = v_ℓ(D) mod 3,  c_p(ℓ) = ind χ_3,p(ℓ),
```
on a candidate small-prime lattice `S`. **Data cost (measured):** one clean split
good prime per lattice generator — `6` primes for the 6-prime fourfold lattice
`{2,3,5,7,11,13}`, `2` primes for the 2-prime sixfold lattice `{2,3}`. Bad primes
(where the fibre is singular) are detected as gate failures and skipped; e.g. M2
skips `p=7` and runs to `p=61` for its sixth clean equation. Results: M1 → `2`,
M2 → `30 = 2·3·5`, M3 → `4 = 2^2`, S6 → `36 = 2^2·3^2`, all matching truth.

This tier is **provably coarse** (Part 3): two different, non-isogenous covers
(`f=x(x-1)`, `g=(x-2)(x-3)(x-4)`) and (`f=x(x-1)`, `g=(x-2)(x-4)(x-6)`) both have
`D ≡ 2 mod cubes`; their freeze streams are **identical** at every prime while
their angle streams **differ** at every prime.

**Tier 2 — angle stream ⟹ the ISOGENY CLASS of `B`.**
By **Faltings' isogeny theorem**: for abelian varieties `A, B` over a number field
`K`, the following are equivalent —
  (a) `A` and `B` are `K`-isogenous;
  (b) `L(A,s) = L(B,s)`;
  (c) for almost all `v`, `char.poly(Frob_v | T_ℓ A) = char.poly(Frob_v | T_ℓ B)`;
  (d) `V_ℓ(A) ≅ V_ℓ(B)` as `G_K`-representations (Tate conjecture for endomorphisms
      of abelian varieties over number fields + semisimplicity of the Tate module).
The full angle stream **is** the collection (c); hence it determines the `K`-isogeny
class of `B` **unconditionally**. Reference: G. Faltings, *Endlichkeitssätze für
abelsche Varietäten über Zahlkörpern*, Invent. Math. **73** (1983), 349–366
(the isogeny theorem is a consequence of the Tate conjecture proved there; English
exposition in Cornell–Silverman, *Arithmetic Geometry*, 1986).

Two isogeny-class invariants are read directly off the stream in Part 2:
- **signature** — balanced `(g_W/2, g_W/2)` iff the freeze is a root of unity at
  every good prime (M1 → `(2,2)`, S6 → `(3,3)`); otherwise the exact Hodge
  signature is the `π`-adic Newton pair `{v_π(det), g_W − v_π(det)}` of the
  `Z[ζ_3]` determinant (the superelliptic `y^3=f`, `deg f = 5`, reads `(1,3)`);
- **decomposability** — real rails (`Π_W` has real coefficients ⟺ `P_B = Π_W^2` ⟺
  `B` isogenous to a square) vs genuinely complex `Z[ζ_3]` rails (`W` not
  conjugation-closed ⟹ simple-type, `End^0 = Q(√-3)`).

**Tier 3 — NEITHER stream ⟹ the specific member within the isogeny class.**
Faltings delivers isogeny, not isomorphism. The specific principally-polarized
member, and the transcendental/fine moduli coordinate, are **L-invisible**: this is
the abelian-variety avatar of the K3 radial finding one floor down (GRADE4 item 4;
`ledger↔cycle-filtration`), where non-isomorphic objects sharing transcendental
data are inseparable in the count stream. In particular the specific `(f,g)` is
**not** recoverable — even the full angle stream fixes only the isogeny class, and
`(f,g)` within a class is free.

---

## A decoupling finding (correction to the item-39 tell)

Item 39 pre-registered "uniform freeze order 1 **and** real rails" as the joint
decomposability tell of the Schoen bielliptic member. This run separates the two
signals: the member `f=x(x-2)`, `g=(x-3)(x-4)(x-5)` has `D = 64 = 4^3` (a cube), so
its freeze order is **uniformly 1**, yet its rails are **genuinely complex** — order
uniformity, not decomposability. Hence:
- **freeze-order uniformity** ⟺ `D ∈ (Q*)^3` — a Tier-1 (discriminant-class) fact;
- **rail reality** ⟺ `B` isogenous to a square — a Tier-2 (isogeny-class) fact.
The Schoen bielliptic member carries both because it is genuinely decomposable with
trivial discriminant class; a generic cover can carry the first without the second.

---

## The inversion's principled boundary (statement)

> **Carrier data ⟹ (isogeny class of the Prym `B`, `D mod cubes`, signature,
> decomposability class, bad-prime set, `K = Q(√-3)`).** The recognition-loop
> construction recipe consumes exactly the isogeny class together with the
> discriminant class `D mod cubes`. It needs no finer datum, with one named
> exception: the specific member within the isogeny class, which by Faltings is
> provably absent from the L-function (the L-invisible fine-moduli coordinate of
> Tier 3). That absence is the inversion's boundary — a theorem about what the
> carrier stream cannot see, not an incompleteness of the reading.

Register: everything in Tiers 1–2 is recovered blind and graded correct; the Tier-3
boundary is stated at exactly theorem strength (Faltings, unconditional). No RH/GRH
enters; the cited inputs are Faltings' isogeny theorem and the classical Gauss/
Jacobi-sum theory already used in the freeze-order mechanism.
