# Review — Helix–Frobenius / L-function Phasor formalization

This is a code review of the Lean 4 / Mathlib development in this repository (the
`*.lean` sources, now under `RequestProject/`). It covers (1) build status, (2)
soundness, and (3) faithfulness of the statements to the informal claims. The
companion paper (`helix_phasor_model.tex`/`.pdf`), the Python reference modules,
and the Markdown spec were read as context but were not independently re-derived.

## Verdict

The Lean development is **sound and intellectually honest**. After the build
repairs described below, the whole library compiles on its pinned toolchain
(Lean v4.31.0 / Mathlib v4.31.0) with **no errors and no warnings**, contains
**no `sorry`, `admit`, `axiom`, `native_decide`, or `@[implemented_by]`**, and
every theorem sampled depends only on the three standard Mathlib axioms
`{propext, Classical.choice, Quot.sound}` — i.e. no construction-specific axiom.
This matches the claim made in `README.md`.

Crucially, the project does **not** claim to prove the Riemann Hypothesis or GRH,
and the statements are formulated so that they cannot be mistaken for such a
claim (see "Faithfulness" below). It is, as advertised, a faithful geometric
*re-encoding* of Dirichlet L-functions and their critical-line zeros, not a new
theorem about where those zeros lie.

## 1. Build status

As delivered, the project **did not build**, for three reasons; the first two are
genuine repository bugs and have been fixed.

1. **File layout (fixed).** The sources sat at the repository root, but every
   cross-file import uses `import RequestProject.<Module>` and the lakefile lists
   `globs = ["RequestProject.+"]`. With the files at the root these imports could
   not resolve and the default build target compiled nothing. The 11 `.lean`
   files were moved into `RequestProject/` (via `git mv`), matching both the
   imports and the `README` description.

2. **Unused, missing `Hammer` dependency (fixed).** `lakefile.toml` required
   `Hammer` (LeanHammer) from git `main`, and the manifest listed it plus its
   transitive deps (`Duper`, `premise-selection`, `auto`), but no source file
   imports any of them — the only import is `import Mathlib`. The `Hammer`
   package directory was absent, which made `lake` abort before doing anything.
   The unused `Hammer` requirement was removed from `lakefile.toml` and the
   manifest re-resolved. (If interactive LeanHammer use is desired it can be
   re-added; it is not needed to build or check the library.)

3. **Toolchain.** The project pins Lean/Mathlib **v4.31.0**. The build was
   performed against that pinned toolchain (Mathlib oleans fetched from cache),
   and succeeds cleanly. `lean-toolchain` and `lakefile.toml` remain on v4.31.0.

After these fixes: `lake build` ⇒ **"Build completed successfully (8569 jobs)"**,
zero errors, zero warnings.

## 2. Soundness

- **No incomplete proofs.** A scan of the sources finds no `sorry`/`admit` and no
  `axiom`/`@[implemented_by]` declarations (the only textual matches are
  doc-comments asserting sorry-freeness).
- **Axiom footprint.** `#print axioms` on a representative set of headline
  results — including `carrierZero_iff_L_zero`, `CarrierZeros_eq`,
  `DirichletCarrierZeros_eq`, `dirichlet_strip_tendsto_LFunction`,
  `eta_strip_tendsto`, `phasor_summable`, `finiteCarrier_tendsto`,
  `frobeniusBlock_det_one`, `frobeniusBlock_unitary`,
  `integral_atomicMeasure_eq`, `faithful_projection_zeta`,
  `fiber_accumulates_to_L`, `scaleBalanced_iff`, `not_scaleBalanced_of_ne`,
  `completedRiemannZeta_critical_line_real`,
  `unconditional_frobenius_eigenstate` — reports
  `[propext, Classical.choice, Quot.sound]` in every case.

## 3. Faithfulness and non-vacuity

The substantive analytic content is real and correctly stated:

- **Phasor representation / convergence** (`LFunctionPhasor.lean`,
  `ClosedForm.lean`): the truncated phasor sums `∑_{n<N} χ(n) n^{-s}` converge to
  `L(s,χ)` for `Re s > 1` (`fiber_accumulates_to_L`,
  `finiteCarrier_tendsto_LFunction`), non-principal character block sums vanish
  and partial sums are bounded (`character_block_sum_eq_zero`,
  `character_partialSum_norm_le`), and these extend across the strip
  (`dirichlet_strip_tendsto_LFunction`, `eta_strip_tendsto`). These are genuine,
  non-trivial theorems.
- **η ↔ ζ on the critical line** (`ClosedForm.lean`): `etaTrivial_eq_zero_iff`
  uses the non-vanishing of the correction factor `1 − 2^{1−s}` on `Re s = ½`
  (`one_sub_two_cpow_ne_zero_on_critical_line`) to prove `η(½+iy)=0 ⇔ ζ(½+iy)=0`.
  Correct and non-vacuous.
- **Geometry / area law** (`AreaLaw.lean`, `HeightGrowthActive.lean`): the
  Archimedean-helix carrier radius grows like `√n`, and `σ = ½` is the unique
  exponent balancing that growth (`scaleBalanced_iff`,
  `sigma_half_is_scale_critical`). Honest asymptotic statements.
- **Functional-equation / reality** (`HelixCollapseReality.lean`): the completed
  zeta is real on the critical line; reflection `s ↦ 1−s` fixes exactly
  `Re s = ½`. Backed by Mathlib.

Two points a reader should keep in mind (these are *framing*, not errors):

- **Some "boxed" zero-equivalences are definitional.** The "carrier" is *defined*
  as the L-function on the critical line (`carrier χ y := LFunction χ (½+iy)`,
  `Feta y := etaTrivial(½+iy)`, `Fchi y := LFunction χ (½+iy)`). Consequently
  `carrierZero_iff_L_zero`, `Feta_eq_zero_iff`, `Fchi_eq_zero_iff` are `Iff.rfl`
  and `CarrierZeros_eq`/`DirichletCarrierZeros_eq` are immediate. They faithfully
  package "the carrier vanishes ⇔ L vanishes", but the mathematical work that
  justifies calling this object the *phasor carrier* is the separate convergence
  layer (`*_tendsto_LFunction`, the strip-extension theorems), not these
  identities themselves.

- **The "Hilbert–Pólya / Frobenius eigenstate" results are constructions, not a
  spectral proof.** `vonNeumannOp γ = γ • id` on `ℂ` trivially has eigenvalue
  `γ`, and `diagOp d` is multiplication by a real diagonal, hence self-adjoint
  with real spectrum by construction. These *realize* each zero ordinate as an
  eigenvalue of a hand-chosen operator; they do not derive the reality of the
  zeros from an independently given operator. The docstrings are appropriately
  worded ("design", "realization", and explicitly "not the claim that all
  analytic zeros lie there (RH/GRH), which is left open").

The naming throughout is evocative ("Frobenius", "explicit formula", "faithful
projection", "Hilbert–Pólya"), but the docstrings consistently and correctly
scope each statement and disclaim RH.

## 4. Changes made during this review

- Moved the 11 `*.lean` sources into `RequestProject/` so imports resolve and the
  default target builds them.
- Removed the unused `Hammer` dependency from `lakefile.toml`; re-resolved
  `lake-manifest.json` for the pinned Mathlib v4.31.0.
- Eliminated all 13 build-time lint warnings at the root (no linters disabled):
  - `RequestProject/ClosedForm.lean`: added `omit [NeZero q] in` before the eight
    theorems that do not use that instance; renamed the deprecated
    `MeasureTheory.integral_finset_sum_measure` to `integral_finsetSum_measure`;
    dropped three unused `simp` arguments (`hi'`).
  - `RequestProject/FrobeniusSimilitude.lean`: dropped the unused `simp`
    arguments `Matrix.head_cons`, `Pi.mul_apply`, `Pi.one_apply`.

No proof was weakened and no statement was changed by these edits; the axiom
footprint is unchanged.

## 5. Recommendation

The development is in good shape: it builds cleanly on its pinned toolchain, is
free of `sorry`/axioms beyond Mathlib's standard three, and its statements are
faithful and honestly scoped. The only conceptual caveat for a future reader is
the distinction in §3 between the definitional zero-equivalences and the
underlying convergence theorems, and the constructive (rather than spectral)
nature of the Hilbert–Pólya/Frobenius eigenstate results — all of which the
source docstrings already make explicit.
