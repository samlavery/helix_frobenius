# If this development *claimed* to prove RH/GRH, how would you disprove it?

This note answers a hypothetical. The project explicitly does **not** claim the
Riemann Hypothesis (RH) or the Generalized Riemann Hypothesis (GRH) — its
docstrings and `README` say so, and `REVIEW.md` confirms the statements are
scoped so they cannot be read as such. The question here is: *suppose* it did
claim RH/GRH — what would refuting that claim look like?

There are two genuinely different things one could mean by "disprove it," and
they require completely different work.

---

## Sense A — Disprove RH itself (refute the *mathematics*)

This means: produce a counterexample to RH, independent of any Lean file.

- **What you would have to exhibit.** A complex number `s` with
  `riemannZeta s = 0`, `s` not a trivial zero (`¬ ∃ n, s = -2*(n+1)`), `s ≠ 1`,
  and `s.re ≠ 1/2`. For GRH: a Dirichlet character `χ` and `s` with
  `LFunction χ s = 0` in the critical strip with `s.re ≠ 1/2` (away from trivial
  zeros). A single such zero kills RH/GRH and therefore any purported proof.
- **Why this is not available today.** No off-line nontrivial zero is known; more
  than 10^13 zeros have been verified to lie exactly on `Re s = 1/2`, and RH is
  widely believed true. So Sense A is not a practical route to "disprove" a
  claimed proof — if RH is true, no counterexample exists.
- **Consequence.** If a Lean term of type `RiemannHypothesis` (below) genuinely
  type-checked with a clean axiom footprint, it could *not* be disproved in Sense
  A; it would simply be correct. That is exactly why a claimed proof must instead
  be audited in **Sense B**.

---

## Sense B — Disprove the *claim* that the Lean artifact proves RH (audit the formalization)

This is the realistic route, and it is how every "I proved RH in Lean" artifact
is actually refuted. You do **not** argue with the kernel — if Lean accepts a
term, it has a proof *of the stated type*. You attack the gap between **the type
that was proved** and **the type RH actually is**. Concretely, you run the
following checklist; finding *any* failure refutes the claim.

### 0. The canonical target

Mathlib already pins down what must be produced. RH is the proposition

```lean
-- Mathlib/NumberTheory/LSeries/RiemannZeta.lean
def RiemannHypothesis : Prop :=
  ∀ (s : ℂ) (_ : riemannZeta s = 0) (_ : ¬ ∃ n : ℕ, s = -2 * (n + 1)) (_ : s ≠ 1),
    s.re = 1 / 2
```

A real proof must yield a term `myProof : RiemannHypothesis` (or a statement
provably equivalent to it). GRH is the analogue for `LFunction χ`. **The whole
audit reduces to: is the theorem you proved actually (defeq/`α`-equivalent to)
this — and is it proved cleanly and non-vacuously?**

### 1. Statement check — is the conclusion really RH?

The single most common defect. Verify the proved theorem:

- **quantifies over all `s : ℂ`** in the strip (an arbitrary zero), **not** over a
  pre-restricted family that already lives on the line;
- **concludes `s.re = 1/2`** (the actual content), rather than something weaker;
- **handles trivial zeros and the pole `s = 1`** the same way Mathlib does.

> Applied to this repo: the headline "zero" results quantify over `y : ℝ` and the
> point `1/2 + i*y`. There `Re = 1/2` is *baked into the input*, so the statement
> says "zeros that lie on the line lie on the line." That is true and useful for a
> geometric re-encoding, but it is **not** RH: it never ranges over off-line `s`,
> so it cannot constrain where zeros are. If such a theorem were relabeled "RH,"
> exhibiting this — the universal quantifier is over the line, not over `ℂ` — is
> the disproof of the claim.

### 2. Definitional-circularity check — is the object defined to be its own answer?

Inspect every `def` the theorem rests on and ask whether the "carrier"/operator/
object is *defined as* the very thing it is supposed to characterize.

> Applied to this repo: `carrier χ y := LFunction χ (1/2 + i*y)`,
> `Feta y := etaTrivial (1/2 + i*y)`, `Fchi y := LFunction χ (1/2 + i*y)`. Hence
> `carrierZero_iff_L_zero`, `Feta_eq_zero_iff`, `Fchi_eq_zero_iff` are `Iff.rfl`,
> and `CarrierZeros = {y | L(1/2+iy)=0}` is immediate. These honestly package
> "carrier vanishes ⇔ L vanishes," but they carry **zero** information about the
> *location* of zeros. If a circular identity like this were dressed up as RH, the
> disproof is to `unfold` the definitions and show the `Iff` is `rfl` — a
> tautology, not RH.

### 3. Non-vacuity / hypothesis check — is it true only because it says nothing?

- Confirm no hypothesis secretly assumes the conclusion (e.g. an `(hs : s.re =
  1/2)` premise, or a domain restricted to the line).
- Confirm the hypothesis set is **satisfiable**: a theorem with contradictory
  premises proves everything and proves nothing. (`lean_minimal_hypotheses`, or
  instantiating the premises with a witness, exposes this. Watch for `exfalso` /
  `by_contra` that close the goal from an impossible context rather than by a real
  contrapositive.)
- Confirm the conclusion is not `True`, `0 = 0`, or anything defeq to it.

### 4. Spectral / "Hilbert–Pólya" check — is reality of the spectrum derived or assumed?

A Hilbert–Pólya proof must (i) define a self-adjoint operator **independently** of
the zeros, and (ii) *prove* its spectrum equals the zero set; reality of a
self-adjoint spectrum then forces `Re s = 1/2`. The fatal shortcut is feeding the
(assumed-real) zero ordinate *into* the operator.

> Applied to this repo: `vonNeumannOp γ = γ • id` and `diagOp d` (multiplication by
> a real diagonal `d`) are self-adjoint with real spectrum **by construction**,
> with the ordinate `γ` supplied by hand. They *realize* each zero ordinate as an
> eigenvalue; they do not *derive* reality from an independent operator. If this
> were called an RH proof, the disproof is: the operator is built from the very
> ordinate whose reality is at issue — circular; step (ii), "spectrum = zero set
> proved independently," is missing. (The docstrings already say "design /
> realization," not proof.)

### 5. Soundness-footprint check — is it actually unconditional and complete?

Even a correctly *stated* `RiemannHypothesis` term is refuted as a *proof* if:

- it contains `sorry`/`admit` anywhere in its dependency tree;
- `#print axioms myProof` shows anything beyond `{propext, Classical.choice,
  Quot.sound}` — e.g. an extra `axiom`, or `Lean.ofReduceBool`/`native_decide`
  used to "decide" an infinite claim, or an `@[implemented_by]` swapping in
  unverified code;
- a premise quietly assumes RH/GRH or an equivalent (then it is conditional, not a
  proof).

> Applied to this repo: this check currently **passes** (no `sorry`/axioms beyond
> the standard three, verified via `#print axioms` on the headline theorems) — but
> that is precisely *because* the statements are the honest geometric ones of
> §§1–4, not RH. A clean footprint certifies "the stated theorems are proved," not
> "RH is proved."

---

## Summary

- **Sense A (disprove RH):** find one nontrivial zeta/L-zero with `Re s ≠ 1/2`.
  None is known; infeasible today; if the artifact really proved RH it could not be
  beaten this way.
- **Sense B (disprove the claim):** the practical route — show the proved
  proposition is not Mathlib's `RiemannHypothesis`. The failure is almost always
  one of: (1) the quantifier ranges over the line, not over `ℂ`; (2) the object is
  *defined* as the L-function, so the key `Iff` is `rfl`; (3) vacuous/over-strong
  hypotheses; (4) the "operator" is built from the assumed-real ordinate, so its
  real spectrum is assumed, not derived; (5) a `sorry` or a non-standard axiom.

For *this* repository, none of these is hidden: the statements are deliberately
the honest §1–§4 versions and the footprint is clean — which is exactly why the
project correctly advertises that it does **not** prove RH/GRH. A claimed RH proof
would have to survive all of checks §1–§5 against `RiemannHypothesis`; the moment
any one fails, the claim is disproved without ever touching a zero of `ζ`.
