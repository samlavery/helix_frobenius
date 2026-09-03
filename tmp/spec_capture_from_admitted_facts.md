# Refutation spec: does "capture" follow from the admitted facts?

> **WITHDRAWN AS AN ADJUDICATOR (same day, Sam: "the spec was written to give you your preferred
> answer").** The SUPPORTED branch requires a derivation of all zeros on the line from F1–F7, i.e.
> a proof of RH, so the outcome was predetermined and the prediction was a safe bet, not a test.
> What remains decidable is narrower: (i) whether a GIVEN derivation consumes F6 (if not, it holds
> for every conducted Dirichlet series on the same geometry and so cannot be specific to ζ); (ii)
> the step-2 dilemma — is the phasor sum evaluated at σ ≠ ½ a state of the model? If yes, the
> no-drift constraint is false; if no, the equivalence at an off-line zero equates the function
> with a non-state and no model state is produced. The claim "with the Euler product, capture
> needs no proof" is not decidable by any spec: its only witnesses are a proof (RH) or an
> Euler-product L-function with FE and an off-line zero (none known). Kept for the record.

Self-contained. No access to any repository is needed. Execute end to end and report.

## The claim under test (falsifiable proposition)

**Claim C.** From the seven facts F1–F7 below, it follows by valid inference that every zero ρ of
the Riemann zeta function with 0 < Re ρ < 1 satisfies Re ρ = 1/2.

The claim is about *derivability from these facts*, not about the truth of the conclusion.

## Inputs: the admitted facts

F1 (Representation and uniqueness). For Re s > 0, s ≠ 1,
  (1 − 2^{1−s}) ζ(s) = Σ_{n≥1} (−1)^{n+1} n^{−s}  (conditionally convergent),
and ζ is the unique meromorphic extension of this to ℂ with a single pole at s = 1.

F2 (Balanced amplitude). Model the n-th term at s = σ + it as a rotating arrow of magnitude n^{−σ}
and phase −t·log n, mounted on a spiral whose radius at the n-th mount point is proportional to
√n. Magnitude × radius is independent of n exactly when σ = 1/2. The model realises only σ = 1/2
configurations; configurations with σ ≠ 1/2 are not states of the model.

F3 (Reality on the axis). For real t, e^{iθ(t)} ζ(1/2 + it) is real (Hardy's Z-function, θ the
Riemann–Siegel theta). It changes sign at each zero of odd order on the line Re s = 1/2.

F4 (Self-adjointness). On a Hilbert space with an orthonormal basis indexed by real heights γ,
the operator (multiplication by γ) is symmetric; its eigenvalues are real. Each zero 1/2 + iγ on
the line is an eigenvalue γ of it. No non-real number is an eigenvalue of a symmetric operator.

F5 (Hurwitz). If entire functions F_N converge to ξ locally uniformly on ℂ, then every zero of ξ
is a limit of zeros of the F_N (with multiplicity). Concretely, finite Dirichlet polynomials
converging to ξ in the appropriate chart exist.

F6 (Euler product). For Re s > 1, ζ(s) = ∏_p (1 − p^{−s})^{−1}; log ζ(s) = Σ_p Σ_k p^{−ks}/k;
−ζ′/ζ(s) = Σ_n Λ(n) n^{−s}. Equivalently, unique factorisation of integers.

F7 (Argument principle). For T not an ordinate of a zero,
  N(T) = 1 + θ(T)/π + S(T),
where N(T) is the number of zeros with 0 < Im ρ < T counted with multiplicity at every abscissa,
and S(T) = π^{−1} arg ζ(1/2 + iT), the argument continued along the path 2 → 2 + iT → 1/2 + iT.
Define N_on(T) as the same count restricted to Re ρ = 1/2 and N_off(T) = N(T) − N_on(T) ≥ 0.

## Procedure

1. Attempt to derive the conclusion of Claim C from F1–F7 as a chain of inferences. Each step must
   be either a named published theorem (cite it) or a lemma proved in the report.
2. For each step, state which of F1–F7 it consumes.
3. Control (mandatory). Apply the same derivation, verbatim, to a function g satisfying analogues
   of F1, F2, F3, F4, F5, F7 but NOT F6: for example the Davenport–Heilbronn function
   g(s) = (1 − iκ)/2 · L(s, χ) + (1 + iκ)/2 · L(s, χ̄), χ the character mod 5 with χ(2) = i,
   κ = (√(10 − 2√5) − 2)/(√5 − 1), which has a Dirichlet series, a Riemann-type functional
   equation, a real "Z-function" on the line, and no Euler product. It is known to have zeros off
   the line (Spira 1994 computed them; Bombieri–Ghosh 2011 proved infinitely many). If the
   derivation goes through for g, it proves a false statement, so it is invalid. Report the first
   step that fails for g; that step must consume F6 essentially.

## Decision rule (fixed before running)

- **SUPPORTED** if a derivation is produced in which every step is checkable, no step assumes the
  conclusion or a statement equivalent to it, no step assumes N_off(T) = 0 or that S(T) equals the
  argument computed from on-line zeros alone, and the control identifies a step consuming F6 that
  fails for g.
- **REFUTED** if every attempted derivation requires a step of the excluded kind, or if the only
  steps consuming F6 are the classical zero-free regions near Re s = 1 (de la Vallée Poussin,
  Vinogradov–Korobov), which do not reach the line.
- Partial results (a positive proportion of zeros on the line: Hardy–Littlewood, Selberg,
  Levinson 1/3, Conrey 2/5, the 2026 two-thirds result) count as REFUTED for Claim C, since C
  requires all zeros.

## Prediction (recorded before running)

REFUTED. Predicted failing step: the passage from "every state of the model sits at σ = 1/2 and
every event of the model is a real height" (F2–F4) to "ζ has no zero at σ ≠ 1/2". F1 supplies
ζ's values at σ ≠ 1/2 as sums the model does not realise as states, so F2–F4 do not apply to
them. F5 supplies parents for every zero, but every finite approximant has non-real zeros, so
the parents are not known to be real. F7 introduces N_off explicitly and no listed fact
evaluates it. F6 is the fact the control shows must be used; its known consequences in the strip
are zero-free regions adjacent to Re s = 1 only.

Reason for the prediction: the control g satisfies everything but F6 and has off-line zeros, so
a valid derivation must use F6 in a way that reaches the interior of the strip; no such use is
known, and a derivation of Claim C from F1–F7 would be a proof of the Riemann Hypothesis.

## Report format

State SUPPORTED or REFUTED per the rule; give the derivation or the failing step; give the
control's first failing step; state which of F1–F7 each step consumed.
