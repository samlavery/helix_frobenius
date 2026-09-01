# Refutation spec: inhabiting a minimal Hilbert–Pólya door for ζ

Self-contained; no access to any private repository is needed or assumed.

## Claim under test (falsifiable)

From the following known, unconditional inputs alone —

1. the Hadamard product / partial-fraction expansion of ξ′/ξ over the
   nontrivial zeros (ξ the completed Riemann xi);
2. the functional equation ξ(s) = ξ(1−s), and realness of ξ on the
   critical line;
3. the Euler product / the Dirichlet series −ζ′/ζ(s) = Σ Λ(n) n^{−s} on
   Re s > 1, with Λ(n) ≥ 0;
4. the classical zero-free region, R.–v. Mangoldt counting, Littlewood's
   ∫S = O(log) bound;
5. numerical verification that all zeros with |Im ρ| ≤ 634.5 lie on the
   critical line —

**no proof is derivable of any of the following:**

(A) There exist a complex inner-product space E, a symmetric linear map
    T : E → E, and, for every nontrivial zero ρ = β + iγ of ζ, an
    eigenvector of T with eigenvalue γ − i(β − 1/2).

(B) For every nontrivial zero ρ = β + iγ, the number γ − i(β − 1/2) is
    real (equivalently: equals log Z for some real Z > 0).

(C) There is a sequence of entire functions F_n converging locally
    uniformly to Ξ(z) := ξ(1/2 + iz), with every F_n having only real
    zeros.

## Procedure

Attempt to construct (A), (B) or (C) from inputs 1–5, one focused
session. For (C), two known instantiations and their status should be
checked first: truncations of the Fourier-integral representation of Ξ
possess complex zeros (Csordas–Norfolk–Varga), and the heat-flow family
H_λ is real-rooted exactly for λ ≥ Λ, where Λ ≥ 0 (Rodgers–Tao) and
Λ ≤ 0.22 (Polymath15) — so real-rootedness of H_λ for all λ > 0 is
equivalent to RH, not a supply of it.

## Decision rule (pre-registered)

- A verified unconditional construction of (A), (B), or (C): REFUTES the
  claim (and constitutes a proof of RH).
- A construction conditional on unproven hypotheses, or no construction:
  SUPPORTS the claim.

## Predicted outcome, with reason

SUPPORTED. (B) is verbatim the reality of the zeros; (A) implies (B) by
realness of symmetric eigenvalues; (C) implies (B) by Hurwitz. Each
proposition contains the conclusion. Sharp point worth independent
scrutiny: inputs 1, 2, 4, 5 are shared by RH-false comparison objects
(Davenport–Heilbronn class), so any refuting construction must consume
input 3 — the Euler product / positivity — essentially, and no published
argument extracts zero-reality from it. If the independent attempt finds
one, the claim dies and that is the better outcome.
