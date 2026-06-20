# Helix–Frobenius

A three-dimensional geometric tool for the **vanishing points of Dirichlet _L_-functions**: a
double-ended chiral helix carrier on which a phasor fiber accumulates; the crossings where the
accumulation cancels coincide with the zeros of the Riemann zeta function and Dirichlet
_L_-functions. It is a tool — it makes no claim about the Riemann Hypothesis.

## Contents

- **`paper/helix_phasor_model.tex`** (and `.pdf`) — the paper.
- **`RequestProject/`** — the Lean 4 / Mathlib formalization. Every named theorem compiles with no
  `sorry`; the kernel axiom footprint is `{propext, Classical.choice, Quot.sound}` (the three
  standard Mathlib axioms), with no construction-specific axiom.
  - Build: `lake exe cache get && lake build` (requires [`elan`](https://github.com/leanprover/elan);
    toolchain pinned in `lean-toolchain`, dependencies in `lake-manifest.json` — Mathlib v4.31.0).
- **`helix_phasor_tool.py`** — a self-contained reference implementation (**NumPy + stdlib only**;
  no mpmath, no zeta routine). It builds the carrier, rides the fiber, and locates the vanishing
  points, comparing them against a published table of zeros (used only for the diff column).
  - Run: `python3 helix_phasor_tool.py`

## What it is

Integers sit at uniform arclength `Δ = π/3` on a growing-radius helix; a fiber `∑ χ(n) n^{−s}` rides
it and accumulates phasors. The angular winding is a log-free, completely multiplicative character
built from prime angles by the fundamental theorem of arithmetic; the logarithm enters only in the
external bridge `wind n ↔ n^{it}` that identifies the geometric winding with the analytic phasor.
The fiber's vanishing points — where the phasors cancel — are the zeros of `L(s, χ)`, verified
numerically for the leading zeros of `ζ` and several Dirichlet `L`-functions.

The correspondence between the paper's statements and the Lean declarations is given by the
identifiers in parentheses throughout the paper (e.g. `frobenius_conjugate_det_one`); the Python
mirrors the same definitions, each annotated with its Lean identifier.
