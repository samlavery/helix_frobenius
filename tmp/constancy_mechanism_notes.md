# The constancy mechanism: channel freeze = annihilator lattice = algebraic class

**Mystery #3, promoted.** The measured signature "channel constancy = algebraicity"
(hodge_portal.py PT2: the degenerate control's six balanced lanes are exact DC with
zero variance) is here promoted to a proven mechanism plus a certified detector. The
statement is that *zero variance of a lane observable is exactly membership in the
annihilator lattice of the Frobenius equidistribution subgroup*, and that on products
of elliptic curves the annihilator lattice is exactly the space of algebraic classes —
the latter by theorem, not conjecture.

The registers are kept strictly separated throughout:

* **Model layer** (unconditional, elementary; formalised in `ChannelConstancy.lean`):
  a finite abelian group / torus with Haar measure, its character theory, the exact
  Parseval variance decomposition, the freeze-⟺-annihilator equivalence, and the
  double-annihilator inversion. Nothing arithmetic enters; it is true as stated.
* **Arithmetic layer** (named published hypotheses): the equidistribution subgroup `H`
  and the exact single-clock moments come from Sato–Tate theory. The freeze *pattern*
  is measure-free (support only); the exact channel *rationals* are the Sato–Tate
  refinement.
* **Bridge layer** ("annihilator classes are algebraic"): Hodge/Tate territory. On
  products of elliptic curves it is a theorem; beyond, it is named, not claimed.

---

## 0. Setup and named inputs

Let `E_1, …, E_g` be elliptic curves over `ℚ`, and for a good prime `p` let
`θ_j(p) ∈ [0, π]` be the Frobenius angle of `E_j`, so `a_p(E_j) = 2√p · cos θ_j(p)`.
Write `α_j(p) = e^{iθ_j(p)}` for the unitarised Frobenius eigenvalue and
`θ⃗(p) = (θ_1(p), …, θ_g(p))`. The object of study is the motive
`M = H¹(E_1) ⊗ ⋯ ⊗ H¹(E_g)` of degree `2^g`, weight `g`; its Hodge/Deligne-torus
reading assigns a channel of frequency `k = Σ ε_j` to each sign vector
`ε ∈ {±1}^g`, and the middle `(m,m)` block is the DC channel `k = 0`
(`EvenWeightDC.lean`, `dc_channel_iff_even_weight`).

**Lane observables.** For `ε ∈ ℤ^g` define the *lane character*
`χ_ε(θ⃗) = e^{i ε·θ⃗} = ∏_j α_j^{ε_j}`. The instrument's Hodge channels are the sign
sums `T_k = Σ_{Σε = k} χ_ε` over `ε ∈ {±1}^g`.

We invoke the following **published theorems** as named hypotheses.

* **(W) Weyl / Peter–Weyl.** For a compact abelian group `A` with Haar measure and
  a function `f = Σ_χ c_χ χ` on `A` (character expansion), the characters are
  orthonormal; hence `E[f] = c_0` and `Var(f) = Σ_{χ ≠ 0} |c_χ|²`. For a closed
  subgroup `H ⊆ 𝕋^g`, a character `χ_ε` of `𝕋^g` restricts to the trivial character
  of `H` iff `ε ∈ H^⊥` (the annihilator), and then `χ_ε ≡ const` on `H`.
  *(Standard; the finite-group form is proved from scratch in the Lean brick.)*

* **(ST) Sato–Tate.** For a fixed non-CM `E/ℚ`, the angles `θ_p` equidistribute in
  `[0, π]` with `μ_ST = (2/π) sin²θ dθ` (Barnet-Lamb–Geraghty–Harris–Taylor 2011,
  via potential automorphy; Clozel–Harris–Taylor, Taylor, Harris–Shin–Thorne). The
  single-clock moments are `∫ cos(2mθ) dμ_ST = −½·[m=1]` (`0` for `m ≥ 2`). For a CM
  `E/ℚ` with CM field `K`, the Sato–Tate group is the disconnected
  `N(U(1)) = O(2)`: half the primes are inert in `K` (`a_p = 0`, `θ = π/2`), half
  split with `θ` equidistributed by the Hecke character; the single-clock moments are
  `∫ cos(2mθ) = ½·(−1)^m` for `m ≥ 1`.

* **(JST) Joint Sato–Tate.** For pairwise non-isogenous non-CM `E_1, …, E_g` the joint
  law of `θ⃗(p)` is the product `μ_ST^{⊗g}` (Harris, "Galois representations,
  automorphic forms, and potential automorphy"; unconditional via BLGHT 2011; effective
  versions Bucur–Kedlaya). Equivalently the joint equidistribution subgroup is the full
  torus of the joint Sato–Tate group `SU(2)^g`.

* **(F) Faltings isogeny theorem.** Two elliptic curves over `ℚ` are isogenous iff they
  have the same `a_p` at all good primes (Faltings 1983; Tate over finite fields;
  Zarhin over finitely generated fields). Hence isogenous legs have *pointwise identical*
  `θ_j`, and the joint equidistribution subgroup collapses along the diagonal of each
  isogeny class.

The **equidistribution subgroup** `H ⊆ 𝕋^g` is then determined by the isogeny/CM data:
group the `g` legs into isogeny classes (blocks) `B_1, …, B_r`; within a block all
angles coincide (by **F**), distinct blocks are independent (by **JST**), so the
connected part of `H` is the *block-diagonal sub-torus*
`H° = { v ∈ 𝕋^g : v_i = v_j whenever i, j lie in the same block }`, of dimension `r`.
CM blocks contribute in addition a *finite part*: the component group of the leg's
Sato–Tate group (`ℤ/2` per CM leg, diagonalised across legs sharing a CM field).

---

## 1. The variance decomposition (Parseval)

> **Theorem 1 (variance decomposition).** Let `μ` be a probability measure on `𝕋^g`
> and `F = Σ_ε c_ε χ_ε` a finite lane combination. Then
> ```
> Var_μ(F) = Σ_{ε, ε'} c_ε \overline{c_{ε'}} · Cov_μ(χ_ε, χ_{ε'}),
>   Cov_μ(χ_ε, χ_{ε'}) = M_{ε−ε'} − M_ε \overline{M_{ε'}},   M_δ := E_μ[χ_δ].
> ```
> If moreover `μ` is Haar measure on a closed subgroup `H ⊆ 𝕋^g`, then
> `M_δ = 𝟙[δ ∈ H^⊥]`, the non-annihilator lanes are orthonormal, and
> ```
> Var_μ(F) = Σ_{ε ∉ H^⊥} |c_ε|²          (Parseval / Weyl form).
> ```

*Proof.* The first identity is the bilinear expansion of the variance using
`χ_ε \overline{χ_{ε'}} = χ_{ε−ε'}`. Under Haar on `H`, orthonormality of the
non-trivial characters of `H` (Peter–Weyl, **W**) gives `E[χ_δ] = 𝟙[δ|_H = 1] =
𝟙[δ ∈ H^⊥]`; substituting collapses the double sum to the diagonal over `ε ∉ H^⊥`. ∎

This is the exact content formalised in `ChannelConstancy.lean` (finite-group model,
uniform measure on a subgroup). The Parseval form is the "maximal-entropy" model — it
keeps only the group `H` and forgets the Sato–Tate density. The arithmetic realisation
uses the first (covariance) identity with the true moments `M_δ`; see §3.

---

## 2. The freeze mechanism (measure-free)

> **Theorem 2 (freeze ⟺ annihilator).** Let `H ⊆ 𝕋^g` be the closed support-subgroup
> of the law of `θ⃗`. For any `ε ∈ ℤ^g`,
> ```
> Var(χ_ε) = 0   ⟺   χ_ε is a.s. constant   ⟺   ε ∈ H^⊥.
> ```
> With `H° = { v : v_i = v_j on each isogeny block }` (from **F**, **JST**), the
> annihilator is the **block-sum lattice**
> ```
> H^⊥ = { ε ∈ ℤ^g : Σ_{j ∈ B_s} ε_j = 0 for every block B_s }.
> ```

*Proof.* `Var(χ_ε) = 1 − |E[χ_ε]|²`, and `|E[χ_ε]| = 1` iff `χ_ε` is a.s. equal to a
constant of modulus one, iff `ε·θ⃗` is a.s. constant mod `2π`, iff `ε` annihilates the
support-subgroup `H`. For the block-diagonal `H°`, writing `φ_s` for the common angle
of block `B_s`, `ε·θ⃗ = Σ_s φ_s (Σ_{j∈B_s} ε_j)`; the `φ_s` range over a set generating
`𝕋^r`, so this is constant iff every block-sum vanishes. ∎

**The key register point.** Theorem 2 is *measure-free*: zero variance depends only on
the support `H`, i.e. only on the isogeny partition, not on the Sato–Tate density. This
is why the detector is robust — it reads the *group*, and the group is an isogeny
invariant. Two consequences fixing the measured cases:

* **Generic** (`H° = 𝕋^g`, `r = g`): `H^⊥ = {0}`; no `{±1}` lane freezes.
* **Degenerate** (`H° = ` diagonal, `r = 1`): `H^⊥ = {Σε = 0}` = the balanced lanes —
  exactly the DC lane of `EvenWeightDC.lean`. The measured six-lane freeze is this.
* **Isogenous** `{θ_1=θ_2, θ_3=θ_4}` (`r = 2`): `H^⊥ = ⟨(1,−1,0,0), (0,0,1,−1)⟩`. Inside
  the `(2,2)` block the *cross-pairing* directions `13|24, 14|23` freeze while the
  *class-separating* direction `12|34` fluctuates — a **directional freeze with an
  address**: the frozen directions name the isogeny partition.

---

## 3. The channel rationals (Sato–Tate refinement)

The exact second moments the instrument checks are *not* the flat Parseval numbers;
they are the covariance form of Theorem 1 with the true moments `M_δ = ∏_{blocks}
c_{type}(·)`. For `ε ∈ {±1}^g` the frequency differences `a_j − b_j ∈ {−2,0,2}` are
even, so only the even-harmonic single-clock moments enter:
`c_{noncm}(0)=1, c_{noncm}(1)=−½, c_{noncm}(m≥2)=0`; `c_{cm}(0)=1, c_{cm}(m)=½(−1)^m`.

> **Proposition 3 (exact channel moments).** For a block partition with types,
> ```
> E|T_k|² = Σ_{a,b ∈ {±1}^g, Σa = Σb = k}  ∏_{blocks B}  c_{type(B)}( ½ Σ_{j∈B}(a_j − b_j) ).
> ```

Instances (all verified to `≤ 0.4σ` on 148,929 primes):

| case | `H`, dim | `E|T_0|²` | `E|T_2|²` | `E|T_4|²` |
|---|---|---|---|---|
| generic | `𝕋^4`, 4 | `99/8` | `7` | `1` |
| degenerate | diagonal, 1 | `36` (Var 0) | `16` (Var 0) | `1` (Var 0) |
| isogenous `{12}{34}` | `𝕋^2`, 2 | `22` | `10` | `1` |

**CM ladder (single leg).** The CM finite part shows as a *partial* freeze of every
higher harmonic: `Var(e^{2imθ}) = 1 − c_{type}(m)²` equals `3/4` for all `m ≥ 1` in the
CM case (`c = ½(−1)^m`), versus `1` for non-CM `m ≥ 2` (`c = 0`). The non-CM harmonic
tower dies after the fundamental; the CM tower never dies. Measured: `32a1` (CM by
`ℚ(i)`), `49a1` (CM by `ℚ(√−7)`) freeze every harmonic to `3/4`; `11a1` to `1`; the CM
legs have exactly half their primes at `θ = π/2` (inert), `11a1` essentially none.

**CM finite part = shared inert set.** Two non-isogenous curves with the same CM field
share the split/inert pattern (the Hecke/Kronecker character of `K`) exactly: their
`θ = π/2` indicators are *identical* — a frozen `ℤ/2` relation in the joint component
group (the finite part of `H`). Measured: `49a1` and its twist `49tw5` (both `ℚ(√−7)`,
non-isogenous) agree on the inert set with probability `1`; `32a1` vs `49a1` (different
fields) are Chebotarev-independent (`P[both inert] = 1/4`).

---

## 4. The inversion (certified detector)

> **Theorem 4 (inversion = double annihilator).** The map `H ↦ H^⊥` is an inclusion-
> reversing bijection between closed subgroups of `𝕋^g` and saturated sublattices of
> `ℤ^g`, with `(H^⊥)^⊥ = H`. Hence the equidistribution subgroup is recovered from its
> frozen lanes:
> ```
> H = ( { ε : Var(χ_ε) = 0 } )^⊥.
> ```
> For a block-diagonal `H°`, the frozen difference relations `e_i − e_j ∈ H^⊥` recover
> the isogeny partition exactly (connected components of `i ∼ j ⟺ e_i − e_j` frozen).

*Proof.* Pontryagin duality for `𝕋^g` (finite-abelian double-annihilator in the model;
Theorem in the Lean brick). For `H°`, `e_i − e_j ∈ H^⊥ ⟺ i, j` share a block, so the
graph of frozen differences is exactly the block partition. ∎

**Certified-detector demonstration** (instrument part (e)). Probing `ε ∈ {−1,0,1}^4`,
collecting the frozen lanes, and taking their annihilator recovers `(dim H, partition)`
correctly for all four cases (generic `4 / {singletons}`, degenerate `1 / {1234}`,
isogenous `2 / {12}{34}`, isogenous-triple `2 / {123}{4}`) — from variance data alone,
no curve labels. **Falsifier:** driving one leg at `2θ` (wrong harmonic) breaks exactly
the relations touching that leg; on the isogenous case leg 0 detaches from leg 1, `dim H`
rises `2 → 3`, and the recovered partition loses the `{0,1}` block — the predicted shift,
observed.

---

## 5. The bridge — algebraicity — at register

The detector reads the annihilator lattice `H^⊥`. The claim to be weighed is:
`H^⊥` classes *are algebraic*. This is the Hodge/Tate content.

* **Frozen ⟹ Hodge/Tate class.** A frozen lane is a Frobenius-invariant of `M` (its
  channel has a constant, non-fluctuating component); on the motivic side these are the
  `(m,m)`-classes fixed by the Mumford–Tate / Sato–Tate group — precisely Hodge classes
  (Betti) and Tate classes (`ℓ`-adic). The annihilator `H^⊥` is the space of such
  invariants because `H` *is* the (identity component of the) Sato–Tate group.

* **Hodge/Tate class ⟹ algebraic, on products of elliptic curves — THEOREM.**
  - *Hodge conjecture for products of elliptic curves:* proven. Checked by Tate
    (unpublished) for powers `E^n`; first full proof by **Imai** (1976), who showed
    `Hg(∏ E_i) ≅ ∏ Hg(E_i)` for pairwise non-isogenous `E_i` and that the Hodge algebra
    is generated in degree one; explicit-forms proof by Murasaki; a uniform modern
    treatment (all of André's conjectures for products of elliptic curves) by
    **B. Kahn** (2023, arXiv:2303.06690, appendix Demarche).
  - *Tate conjecture, divisor case:* proven for abelian varieties by **Tate** (finite
    fields), **Faltings** (number fields), **Zarhin** (finitely generated fields);
    equivalent to `Hom(A,B) ⊗ ℚ_ℓ ≅ Hom_{Gal}(V_ℓ A, V_ℓ B)`.
  - *Tate for products of elliptic curves, arbitrary codimension:* since the Hodge (and
    Mumford–Tate) group is generated in degree one, all Tate classes reduce to products
    of divisor classes; see **Chao Li–Wei Zhang**, "A note on Tate's conjectures for
    abelian varieties" (arXiv:2112.15164) — Tate I holds for abelian varieties whose
    simple factors have dimension `≤ 2`.

> **Corollary (certified algebraic-class detector).** On a product of elliptic curves
> `E_1 × ⋯ × E_g` over `ℚ`, every frozen lane of the portal is an algebraic cycle class,
> and the freeze detector's output — the annihilator lattice `H^⊥` and its recovered
> isogeny partition — is a *certified* readout of the algebra of algebraic classes. The
> mechanism (Theorems 1–4) is unconditional; the algebraicity bridge is theorem-backed
> at exactly this scope by the citations above.

---

## 6. What remains named (register-honest ledger)

* **Mechanism (Theorems 1–4): PROVEN, unconditional.** Elementary character theory;
  the finite-group model is formalised in Lean with the standard footprint. The freeze
  pattern is measure-free; the exact channel rationals follow from the single-clock
  Sato–Tate moments.
* **Equidistribution input (`H` itself): named published theorems.** Sato–Tate,
  joint Sato–Tate (Harris; BLGHT 2011), Faltings. These give that the *measured*
  frozen set equals the *predicted* `H^⊥`. Without them the freeze pattern still holds
  as an identity about whatever subgroup the angles fill; with them that subgroup is the
  arithmetic `H°`.
* **Algebraicity bridge:**
  - *On products of elliptic curves: THEOREM* (Imai/Kahn Hodge; Faltings/Tate/Zarhin +
    degree-one generation Tate). The detector is **certified** on this class.
  - *Beyond products of elliptic curves: NAMED, NOT CLAIMED.* For a general abelian
    variety or motive the Hodge conjecture (exotic Weil classes, e.g. Mumford's example)
    and the Tate conjecture are open; there the detector reads the Hodge/Tate class
    space, and its identification with algebraic cycles is conjectural at exactly the
    strength of those open conjectures.

**Status of Mystery #3 after this note.** The signature "channel constancy =
algebraicity" is now a *proven mechanism* (channel freeze = annihilator lattice of the
Frobenius equidistribution subgroup) and a *certified detector* on **products of
elliptic curves** (frozen lanes are algebraic classes by the Hodge/Tate theorems for
that class), with the recovered address = the isogeny partition and a firing wrong-
harmonic falsifier. The single named remainder is the general Hodge/Tate bridge beyond
products of elliptic curves — carried exactly at the strength of those open conjectures,
never overstated.

*Instruments:* `constancy_mechanism.py` (+ `_results.txt`); Lean model
`RequestProject/ChannelConstancy.lean`; upstream `hodge_portal.py`, `tower_atlas.py`,
`EvenWeightDC.lean`. CM caches `theta_32a1`, `theta_49a1`, `theta_49tw5` (theta_cache
pattern).
