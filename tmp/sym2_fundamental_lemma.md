# The Sym^r fundamental lemma has transparent arithmetic — a clock-identity reduction

**Scope.** This is a structural reduction of the *arithmetic* half
of the beyond-endoscopic fundamental lemma for symmetric-power transfer `GL(2) → GL(r+1)`, `r` even,
obtained from the Satake angle-multiplication and the `symTrace` clock identity. It does not by itself
prove the fundamental lemma (the archimedean transfer factor and the spectral matching remain); it
removes the obstruction I had wrongly called fatal.

## The setup

Beyond-endoscopic transfer of Sym^r sends a GL(2) elliptic class with Satake angle `θ`
(`cosθ = t/2√n`, discriminant `D = t²−4n < 0`) to the GL(r+1) class with Satake angles
`{2kθ : |k|≤m} ∪ {0}` (`r=2m`), i.e. characteristic polynomial
$$(x-1)\prod_{k=1}^{m}\big(x^2 - 2\cos(2k\theta)\,x + 1\big).$$
The fundamental lemma must match the GL(2) Sym^r-weighted orbital integral to the GL(r+1) orbital
integral at this class. The GL(2) orbital weight is (class-number formula / CNF collapse)
`√|D|·L(1,χ_D)` times the archimedean profile; the GL(r+1) weight is the order-zeta `L(1,R)` of the
cubic/degree-`(r+1)` order `R` attached to the characteristic polynomial, times its archimedean
profile. The order-zeta for *irreducible* orders is the Deng–Espinosa Conjecture-A object (open).

## The two facts that make the arithmetic transparent

**1. The transferred classes are reducible.** The rational eigenvalue `1` (the DC clock, present iff
`r` even) makes the characteristic polynomial reducible. So `R` is an order in
`ℚ ⊕ (\text{quadratic})^{\oplus m}`, whose order-zeta is *elementary* (`ζ · L(χ)` with local index
factors), **not** the Conjecture-A object. The obstruction I claimed — Conjecture A — is avoided
because Sym^r never transfers to an irreducible class.

**2. All quadratic factors lie in the single field `ℚ(√D)`.** The `k`-th factor
`x²−2cos(2kθ)x+1` has discriminant `−4sin²(2kθ)`. By the clock identity (`TwoClockWeightLaw.symTrace_exp`)
$$\sin(2k\theta) = \sin\theta \cdot U_{2k-1}(\cos\theta),$$
and `sin²θ = |D|/4n`, so
$$\frac{\operatorname{disc}_k}{D} = \frac{U_{2k-1}(\cos\theta)^2}{4n}\ \in\ \mathbb Q^{\times 2}$$
is a **rational square** — an identity, holding for every `k` and every class. Hence every
transferred quadratic factor generates the *same* field `ℚ(√D)` as the original GL(2) class.

**Consequence.** The arithmetic `L`-value is *identical* on both sides of the fundamental lemma
(same `ℚ(√D)`, hence same `L(1,χ_D)`), so it **cancels in the transfer factor**. What remains is
purely archimedean/Weyl (`U_r` × a ratio of orbital profiles × the `ζ`-pole from the rational
eigenvalue) — computable, and the same object the exact-gauge uniformity already controls.

*Verified:* `sf(D)=sf(D_transf)` for all tested classes, and the `disc_k/D` identity through
Sym²/Sym⁴/Sym⁶ (`$CLAUDE_JOB_DIR/tmp/symr_fl.py`).

## Where the boundary now sits (honest)

- **Cleared:** the arithmetic half of the Sym^r FL — transparent, Conjecture-A-free, whole even
  family, by the Satake + `symTrace` clock identity. This is genuinely new and is the crack in the
  door.
- **Remaining, computable:** the **archimedean transfer factor** `Δ(θ)` = `U_r(cosθ)` × (GL(2) profile
  / GL(r+1) profile) × (`ζ`-pole factor). This is where *proper scaling* (the Satake normalization
  `n^{(k-1)/2}`) and the Eisenstein/`ζ₆`·`μ_6` exact-gauge scaling are the natural tools — the cubic
  discriminant `a²b²−4b³−4a³c+18abc−27c²` carries the `ζ₃`/Eisenstein structure of the degree-3 side.
- **Remaining, harder:** the spectral matching (the transferred residue = a term in the GL(r+1)
  spectrum) — the analogue of Altuğ's Thm 1.1, transported.
- **Beyond scope:** full automorphy on GL(r+1) (for holomorphic GL(2) this is Newton–Thorne 2021 by
  other means; the open frontier is Maass/general fields).

The correction to my earlier claim: the Sym^r FL is **not** out of reach behind Conjecture A — the
clock identity makes its arithmetic transparent. The remaining pieces are archimedean (our home turf)
and a transported spectral identification. Related: [[be-uniformity-proof]], [[gl3-family-universality]],
[[bsd-clocks-program]] (`rank_is_dc_residue`, one mechanism two locations).
