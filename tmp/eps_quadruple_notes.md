# The global root number of the primitive quadruple is +1

**Object.** Let

    M  =  H^1(E_1) ⊗ H^1(E_2) ⊗ H^1(E_3) ⊗ H^1(E_4),
    (E_1,E_2,E_3,E_4) = (11a1, 37a1, 53a1, 61a1),

a pure motive over ℚ of dimension 16 and motivic weight 4, with Hodge numbers
h^{4,0}=1, h^{3,1}=4, h^{2,2}=6, h^{1,3}=4, h^{0,4}=1 (diamond 1,4,6,4,1). Each
E_j is a semistable elliptic curve of prime conductor N_j ∈ {11,37,53,61}. Write
Λ(M,s) = G(s) L(M,s) for the completed L-function, in the analytic normalization
s ↔ 1−s (center 1/2); the functional equation reads Λ(M,s) = ε(M) Λ(M,1−s) with
ε(M) ∈ {±1} because M is self-dual (H^1(E_j) is symplectically self-dual, and a
tensor product of an even number of symplectic self-dual objects is orthogonally
self-dual, hence essentially self-dual with a real sign).

> **Theorem.** ε(M) = +1.

The proof is unconditional: it uses only Deligne's ε-factor formalism, Tate's
local constants, the classification of local root numbers of elliptic curves at
multiplicative reduction, and the Weil bound det H^1(E) = ℚ_ℓ(−1). No hypothesis
on L-functions (RH/GRH, automorphy, analytic continuation beyond the standard
theory) is used, and nothing is circular.

Throughout, ε(M) = ∏_v ε_v(M, ψ_v, dx_v) is Deligne's factorization of the global
constant over all places v of ℚ (Deligne 1973, *Les constantes des équations
fonctionnelles des fonctions L*, Thm 4.1 / 5.x; Tate, *Number theoretic
background*, Corvallis 1979, §3). The product is independent of the global
additive character ψ = ∏ψ_v and the measures; each factor is normalized to
absolute value 1 (root-number normalization), so ε_v ∈ ℂ^× with |ε_v| = 1, and
the global sign is the product of the local *phases*. M is unramified outside
{11,37,53,61,∞}, and ε_v = 1 at every finite unramified place. Hence

    ε(M) = ε_∞(M) · ε_11(M) · ε_37(M) · ε_53(M) · ε_61(M).

---

## Part I — the finite places: every ε_p = +1

Fix a bad prime p ∈ {11,37,53,61} and let j = j(p) be the unique index with
N_j = p (the conductors are distinct primes). At p:

* the leg V := H^1(E_j)_p is **ramified**: E_j has multiplicative reduction at p,
  so its Weil–Deligne representation is the special (Steinberg) representation
  sp(2) up to an unramified twist, with conductor exponent a(V) = 1 and
  dim V = 2 (Rohrlich, *Elliptic curves and the Weil–Deligne group*, in
  *Elliptic curves and related topics*, CRM 1994; Serre–Tate);
* the three legs W_k := H^1(E_k)_p (k ≠ j) are **unramified**: E_k has good
  reduction at p, so W := ⊗_{k≠j} W_k is an unramified representation of the Weil
  group with dim W = 2·2·2 = 8.

Thus M_p ≅ V ⊗ W with V ramified and W unramified.

**Deligne's unramified-twist formula** (Deligne 1973, 5.5.1; Tate, Corvallis,
(3.4.6)): for V arbitrary and W unramified,

    ε(V ⊗ W, ψ, dx) = ε(V, ψ, dx)^{dim W} · det_W(Frob)^{ a(V) + dim(V)·n(ψ) },

where det_W is the (unramified) determinant character of W, Frob a geometric
Frobenius, a(V) the Artin conductor exponent, and n(ψ) the level of ψ. Taking ψ
of level 0 (n(ψ) = 0):

    ε_p(M) = ε_p(V)^{ dim W } · det_W(Frob)^{ a(V) }
           = ε_p(V)^{ 8 } · det_W(Frob)^{ 1 }.

We evaluate the two factors.

**(i) ε_p(V)^8 = +1.** The local root number of an elliptic curve is real,
ε_p(V) = w_p(E_j) ∈ {±1} (w_p = −1 for split, +1 for non-split multiplicative
reduction — Rohrlich, loc. cit.). Any eighth power of ±1 is +1. *This uses no
finer information than ε_p(V) ∈ {±1}, which holds because V is self-dual.*

**(ii) det_W(Frob) = p^{12} > 0, hence contributes phase +1.** For a good-reduction
curve, det H^1(E_k)_p = ℚ_ℓ(−1) (the Weil pairing / Poincaré duality gives
∧^2 H^1 ≅ ℚ_ℓ(−1)), so geometric Frobenius acts on det W_k by p (product of the
two weight-1 Frobenius eigenvalues α_k β_k = p, Weil). For three legs of dimension
2 each,

    det_W = det(⊗_{k≠j} W_k) = ⊗_{k≠j} (det W_k)^{ ∏_{l≠j,k} dim W_l }
          = ⊗_{k≠j} (det W_k)^{4},     det_W(Frob) = (p)^{4}·(p)^{4}·(p)^{4} = p^{12}.

This is a positive real number; its argument is 0, so det_W(Frob)^{a(V)} = p^{12}
contributes the phase +1 to the (unit-modulus normalized) root number.

Therefore **ε_p(M) = (+1)·(+1) = +1 for every p ∈ {11,37,53,61}**, and
∏_p ε_p(M) = +1.

*Robustness.* The finite sign does not depend on split-vs-non-split, on the value
of ε_p(V), or on any delicate special-representation computation: it needs only
(a) ε_p(V) ∈ {±1} raised to the *even* power dim W = 8, and (b) that det_W(Frob)
is a positive power of p. Both are forced by the structure "one Steinberg leg,
three good legs."

**Conductor postdiction.** Since W is unramified, the Artin conductor is
a(M_p) = a(V ⊗ W) = dim(W)·a(V) = 8·1 = 8 at each bad prime (the inertia
representation of V ⊗ W is V^{⊕ dim W}; both tame and Swan parts scale by dim W —
Serre, *Facteurs locaux des fonctions zêta*). Hence the conductor of M is

    Q = ∏_p p^{a(M_p)} = (11·37·53·61)^8,

independently reproducing the exponent 8 in the functional-equation datum G(s).

---

## Part II — the archimedean place: ε_∞ = i^{20} = +1

Deligne's archimedean local constant is determined by the real Hodge structure
(H_B, F_∞), where F_∞ is the infinite Frobenius, a rational involution with
F_∞(H^{p,q}) = H^{q,p} (Deligne 1973, §5; Deligne, *Valeurs de fonctions L et
périodes d'intégrales*, Corvallis 1979, §5.2–5.3). Decomposing H_B ⊗ ℂ into
W_ℝ-representations:

* each Hodge pair (p,q) with p<q contributes the 2-dimensional induced
  representation of gap q−p, with local root number **i^{(q−p)+1}**, with
  multiplicity h^{p,q};
* the middle H^{m,m} (m = w/2, here m = 2) decomposes under F_∞ into a trivial
  part (root number 1) and a sign part (root number i); the sign characters are
  exactly the F_∞ = (−1)^{m+1} eigenvectors. Let n_sgn = dim H^{m,m}(F_∞ =
  (−1)^{m+1}).

Hence

    ε_∞ = i^{ A },     A = Σ_{p<q} (q−p+1) h^{p,q}  +  n_sgn.

**The pair term.** From the Hodge diamond (1,4,6,4,1): pair (0,4) has gap 4,
exponent 5, multiplicity 1; pair (1,3) has gap 2, exponent 3, multiplicity 4. So

    Σ_{p<q} (q−p+1) h^{p,q} = 5·1 + 3·4 = 17.

**The middle split is (3,3), forced.** F_∞ on M is the tensor F_∞ = ⊗_{j} F_∞^{(j)}
of the four infinite-Frobenii. In a Hodge-adapted ℂ-basis {e_j, f_j} of H^1(E_j)
(e_j spanning H^{1,0}, f_j spanning H^{0,1}), F_∞^{(j)} is the swap e_j ↔ f_j
(any elliptic curve over ℝ: F_∞ is an involution interchanging the two Hodge
lines; rescale so it is the plain transposition). The middle H^{2,2} has the
6-element monomial basis indexed by the 2-subsets S ⊆ {1,2,3,4} of "e-slots"
(exactly two factors of type (1,0), two of type (0,1)). The involution F_∞ sends
the basis vector v_S to v_{S^c}; since |S| = 2 and |S^c| = 2 with S ≠ S^c always,
F_∞ has **no fixed vectors** and pairs the six monomials into **three
transposition pairs**. Each pair {v_S, v_{S^c}} contributes one F_∞ = +1
eigenvector (v_S + v_{S^c}) and one F_∞ = −1 eigenvector (v_S − v_{S^c}). Thus

    h^{2,+} = 3,   h^{2,−} = 3.

This uses only F_∞ = ⊗(swap); it is independent of the arithmetic of the four
curves. For m = 2 the sign characters are the F_∞ = (−1)^{m+1} = −1 eigenvectors,
so **n_sgn = 3**.

**Assembling.**

    A = 17 + 3 = 20,   ε_∞ = i^{20} = +1.

---

## Part III — convention calibration (independent check of Parts I–II)

The recipe of Parts I–II is a single algorithm with one convention (the choice
of additive character ψ, absorbed in "root number of the sign character = i").
It is pinned and verified by running it on eight objects whose global signs are
already known in-house / from LMFDB, using the same finite and archimedean
formulas. The finite input is the local root number of Sym^r of a Steinberg
representation: Sym^r(sp(2)⊗χ) = sp(r+1)⊗χ^r, and the twisted special-
representation constant ε(sp(n)⊗χ) = (−χ(Frob))^{n−1} (Tate, Corvallis §4;
Rohrlich) gives, with n = r+1 and χ(Frob) = c ∈ {+1 (split), −1 (non-split)},

    ε_p(Sym^r) = (−c^{r})^{r} = (−1)^r c^{r^2};

and the archimedean input is the formula above. Reduction types (split/non-split) are recomputed from the
Weierstrass models by Tate's algorithm, so no root-number oracle enters the
calibration.

| object | Hodge weight | ε_finite | ε_∞ | ε(total) | known |
|---|---|---|---|---|---|
| H^1(11a1)             | 1 | −1 (split, w=−1)      | i^2 = −1 | **+1** | +1 (rank 0) |
| H^1(37a1)             | 1 | +1 (nonsplit)         | i^2 = −1 | **−1** | −1 (rank 1) |
| H^1(53a1)             | 1 | +1 (nonsplit)         | i^2 = −1 | **−1** | −1 (rank 1) |
| H^1(61a1)             | 1 | +1 (nonsplit)         | i^2 = −1 | **−1** | −1 (rank 1) |
| Sym²(11a1)            | 2 | +1                    | i^{3+1} = +1 | **+1** | +1 |
| Sym³(11a1)            | 3 | −1                    | i^{6} = −1 | **+1** | +1 |
| Sym⁴(11a1)            | 4 | +1                    | i^{8} = +1 | **+1** | +1 |
| 11a1 × 37a1 (RS4)     | 2 | +1                    | i^{3+1} = +1 | **+1** | +1 |
| Sym²(11a1) ⊗ 37a1 (deg 6) | 3 | +1               | i^{8} = +1 | **+1** | +1 |

All nine postdictions hold. Two of them pin the archimedean **middle rule**
uniquely, because self-duality forces ε ∈ {±1} (a real value):

* **Sym²(11a1)** (m=1): the middle vector e·f is F_∞-fixed (F_∞ = +1). Only the
  rule "sign characters = F_∞ = (−1)^{m+1} = +1 eigenvectors" gives n_sgn = 1 and
  a real ε_∞ = i^{3+1} = +1; the alternative gives i^3 (non-real, impossible).
* **Sym⁴(11a1)** (m=2): the middle vector e²f² is F_∞-fixed (F_∞ = +1). Only the
  rule "sign characters = F_∞ = (−1)^{m+1} = −1 eigenvectors" gives n_sgn = 0 and
  a real ε_∞ = i^{8} = +1; the alternative gives i^9 (non-real).

These two even/odd anchors leave no freedom in the middle rule, and it is exactly
the rule applied to the quadruple's (2,2) block. The deg-6 anchor is a genuine
test of the finite rule: at p = 37 the unramified part has *odd* dimension 3, so
ε_37 = w_37(37a1)^3 = w_37(37a1) = +1 depends on 37a1 being non-split — and it
postdicts correctly.

---

## Conclusion

    ε(M) = ε_∞ · ∏_p ε_p = (+1)·(+1)^4 = +1.       ∎

**Published results the proof rests on (all unconditional theorems).**

1. Deligne, *Les constantes des équations fonctionnelles des fonctions L*
   (Antwerp II, LNM 349, 1973): existence and factorization ε = ∏_v ε_v; the
   unramified-twist formula (5.5); the archimedean constants from the Hodge type
   (§5).
2. Tate, *Number theoretic background* (Corvallis, PSPM 33.2, 1979), §3–4:
   local constants, the unramified-twist corollary (3.4.6), and root numbers of
   (twisted) special representations.
3. Rohrlich, *Elliptic curves and the Weil–Deligne group* (CRM Proc. 4, 1994):
   local root numbers of elliptic curves — w_p = −1 (split), +1 (non-split)
   multiplicative; ε_p(E) ∈ {±1} at all p; the archimedean value ε_∞(E) = −1.
4. Weil / Eichler–Shimura / Deligne (Weil conjectures for curves): det H^1(E) =
   ℚ_ℓ(−1), i.e. α_p β_p = p at good primes; the semistable Weil–Deligne type
   sp(2) at multiplicative primes.
5. Serre, *Facteurs locaux des fonctions zêta des variétés algébriques*
   (Sém. DPP 1969/70, exp. 19): Artin conductor / Swan formula, giving
   a(M_p) = dim(W)·a(V) = 8 and Q = (∏ N_j)^8.
6. Standard Hodge theory: F_∞ = ⊗_j F_∞^{(j)} on a tensor product, and F_∞
   interchanges H^{p,q} ↔ H^{q,p}, which forces the (3,3) split of the (2,2)
   block by the swap-pair argument.

The reduction types feeding the calibration were recomputed from the Weierstrass
equations by Tate's algorithm (tmp/sha_hinge.py) and cross-checked against Sage's
`EllipticCurve.root_number()`; the mechanized recipe and its postdiction table
are in tmp/eps_quadruple.py (output tmp/eps_quadruple_results.txt).
