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
- **`focal_closure.py`** — exact harmonic cancellation at the zeros, demonstrated by the
  focal-closure growth locator: the finite 3-D bank (lanes P/M/U riding the carrier) locates its
  own vanishings as lane-balance events, with no L-function call in the loop (published reference
  ordinates enter only the final `|diff|` validation column). Families: `eta`/ζ, real and complex
  Dirichlet characters, Ramanujan Δ (τ built from `η^24`), and elliptic curve 11.a.
  - Run: `python3 focal_closure.py test` (~30 s) or `python3 focal_closure.py demo` (~2–4 min)
- **`carrier_fiber/`** — the finite Python carrier/fiber harness. It keeps the native `pi/3`
  carrier scan, the harmonic pencil marker, and the c1 cumulative carrier-clock validation separate.
  `validate` runs finite-first (channels from the truncated phasor bank); the mpmath analytic
  certificate is opt-in via `--mode analytic`.
  - Run: `python3 carrier_fiber.py test` from `carrier_fiber/`

## What it is

Integers sit at uniform arclength `Δ = π/3` on a growing-radius helix; a fiber `∑ χ(n) n^{−s}` rides
it and accumulates phasors. The angular winding is a log-free, completely multiplicative character
built from prime angles by the fundamental theorem of arithmetic; the logarithm enters only in the
external bridge `wind n ↔ n^{it}` that identifies the geometric winding with the analytic phasor.
The fiber's vanishing points — where the phasors cancel — are the zeros of `L(s, χ)`, verified
numerically for the leading zeros of `ζ` and ten Dirichlet `L`-functions (the quadratic characters
mod the primes 3–31), with the published reference zeros taken from LMFDB and cross-checked against
an mpmath Hurwitz-zeta computation to ~1e-9.

The correspondence between the paper's statements and the Lean declarations is given by the
identifiers in parentheses throughout the paper (e.g. `frobenius_conjugate_det_one`); the Python
mirrors the same definitions, each annotated with its Lean identifier.
