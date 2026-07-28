# Beyond the abelian-cover playbook: the frontier spec

**2026-07-28, session 18a3f704. Status: specification + literature scout. Register
discipline: the Mostaed read is ABSTRACT-ONLY so far — full-text verification required
before any build (literature-before-novelty, hard rule).**

## Why this spec exists

The Patel–Zhang audit (Thm 1.2, read at source 2026-07-16) + the étale-cyclic no-go
close the entire abelian-cover playbook: every constructible Prym specimen (our three
sixfolds, the eightfold, the μ6 pieces) has algebraic Weil classes by cited theorem and
split discriminant by construction. The open Hodge frontier for Weil-type abelian
varieties is therefore exactly the complement, and tonight's dim-6 calibration rung
(B over v²=u³+1: End⁰ = ℚ(ζ₃) certified two-prime, MT = GU(3,3) full, accounting
closed, Weil classes by Schoen/P–Z ⟹ Hodge closed every degree) means the instruments
are calibrated one register below it. Three directions, in order of attack:

## Direction 1 — the rigid/CM sixfolds (Mostaed, arXiv 2603.20268)

Abstract-level read (2026-07-28): McMullen's Kobayashi-geodesic curve V meets the Weil
locus in finitely many (possibly zero) points; at intersections the sixfold has CM with
endomorphism field M = KL; for d ∈ {3,7}, M = ℚ(ζ₄₂) (deg φ(42)=12 ✓ sixfold CM);
the Hodge–Weil classes there are ABSOLUTE HODGE yet inaccessible to all existing
algebraicity theorems (three obstructions: CM isolation, no K-secant structure,
uncontrolled discriminant; Zilber–Pink super-atypicality). The author reduces the
d ∈ {3,7} case to **2816 explicit algebraic equations at ℓ = 43 via Hecke
correspondences**.

WHY THIS IS HOUSE-SHAPED: CM abelian sixfolds with explicit CM field are constructible
from ideal lattices in ℤ[ζ₄₂]; Frobenius = explicit Hecke characters ⟹ point counts =
character sums (the house's native instrument class); "2816 equations at ℓ=43" is a
finite computational surface. TASKS: (1.1) full-text read — verify the abstract claims,
extract the equation system's exact shape and what solving it would prove; (1.2) can
the census/rails instruments address the CM specimen directly (Frobenius data from
Hecke characters, no point-counting loop needed); (1.3) the uncontrolled-discriminant
obstruction vs our lattice/glue machinery (the no-go analysis is exactly a discriminant
computation — same tools, new object).

## Direction 2 — non-abelian étale covers (the P–Z boundary is ABELIAN)

Patel–Zhang cover Pryms of étale ABELIAN covers. Isotypic pieces of étale NON-ABELIAN
covers (smallest: S₃; the 2-dim irrep ρ) are OUTSIDE their theorem — and constructible
+ fiber-product-countable by house methods (the v1 sixfold's S₃ closure shows the
machinery exists; there the S₃ was an ACCIDENT that decomposed B — here it becomes the
design). DESIGN TASK: an everywhere-étale S₃-cover Z → C (exists for any g(C) ≥ 2:
π₁ ↠ S₃), the ρ-isotypic piece B_ρ ⊆ Jac Z, dim = 2(g−1)·? — work out: (2.1) when does
B_ρ carry a Weil-type structure (need a CM/quadratic field acting: compose with a
μ₃-structure on C itself — the (S₃ × ℤ/3)-tower: ρ⊗ω pieces, which is EXACTLY the v1
closure's M_{ρ⊗ω} — but there it arose from a RAMIFIED tower; the étale version is the
new object); (2.2) the glue/discriminant law for non-abelian isotypic lattices (the
cut-glue integral model generalizes: ℤ[S₃]-module structure of H₁ — the uniform-rescale
argument breaks for 2-dim irreps: THE opening the no-go leaves); (2.3) counting: fiber
products over the intermediate quotients + character theory of S₃ (the nonabelian-bit-
by-order memory has the element-order reading machinery).

## Direction 3 — the lattice spec (from the no-go, sharpest form)

Non-split demands det with odd inert-prime valuation or unit ≡ 2 mod 3. The μ6
integral-model verdict: CYCLIC towers give uniform-rescale types (always split) ⟹ the
lattice route needs non-cyclic glue — which is Direction 2 in lattice language, or
non-Prym sources entirely (Direction 1). Conjecture worth proving en route (named
2026-07-16): "étale cyclic ⟹ uniform type scale ⟹ split" as a theorem; the cut-glue
model is the proof frame.

## Priority

1.1 (full-text read) first — cheap, gates everything in Direction 1; then 2.1/2.2 (the
S₃ design math — genuinely new territory with house tools); Direction 1 build if the
read confirms; Direction 3 rides along as the lattice bookkeeping of whichever
construction lands.
