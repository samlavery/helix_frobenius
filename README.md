# Helix–Frobenius

The classical *L*-function is a one-dimensional readout of a three-dimensional object. This
repository contains the object: a **3D state space** carrying a double-ended helix and its
conjugate anti-helix (Archimedean, constant pitch one unit), with two harmonically scaled
carriers running from the origin to infinity. Automorphic functions ride the carriers as
**fibers** — banks of phasors with unique magnitude and rotation, growing continuously in
height. Vanishing is exact focal cancellation of the helix and anti-helix fibers, observed as
conjugate eigenstates of a Gram–von Neumann / harmonic-pencil operator pair; the classical zero
is recovered by a **ledgered projection** (Möbius/Cayley to the unit circle with the radius
booked, then to the line with the angle booked and the logarithm applied) at `y = log z`.

The paper's thesis: the unit-1 chart is cohomologically sub-optimal, and the harmonically scaled
3D frame is the more accurate one. In that frame the paper proves, among other results: the
classical `S(t)` oscillatory term is the registration gap between the two scales — a chart-defect
compensation mechanism, proven unconditionally; symmetric-power functoriality on GL(2) data at
every rank via the Cogdell–Piatetski-Shapiro checklist, with niceness discharged on the carrier;
Sato–Tate for Maass forms; a root-cause analysis and repair of Altuğ's Beyond-Endoscopy
uniformity problem; and **two conditional proofs of GRH**, each resting on a single named
reading — what the Hilbert–Pólya program requires of its spectrum, and whether the *real*
nontrivial zero is the 3D source event or its classical 1D interpretation. Nothing in the paper
asserts RH or GRH: the readings are stated exactly, asserted by no one, and deferred to the
community, with three admissible verdicts (both sound, one, or none).

**Status: preprint draft v0.1 (July 2026), under active revision.** Exposition, numbering, and
section order are unstable between versions; changes are tracked in this repository.

## Layout

- **`automorph/universal.tex`** — the paper (builds to ~106 pp). The GRH worked-example part
  lives in **`automorph/grh_worked_example_draft.tex`** and is `\input` at the boundary between
  the functoriality and Beyond-Endoscopy parts. Build: `pdflatex universal.tex` twice, from
  `automorph/`.
- **`RequestProject/`** — the Lean 4 / Mathlib formalization (150+ files). Every named theorem
  compiles with no `sorry` and no construction-specific axiom; the kernel footprint is exactly
  `{propext, Classical.choice, Quot.sound}` (the three standard Mathlib axioms), audited by
  `#print axioms` lines at the bottoms of the files.
  - Build: `lake exe cache get && lake build` (requires
    [`elan`](https://github.com/leanprover/elan); toolchain pinned in `lean-toolchain` —
    Lean v4.31.0, Mathlib per `lake-manifest.json`).
  - **Entry point:** `RequestProject/HelixResolventCapture.lean` — the GRH capstone file — and
    work backwards. The paper's Evidence I/II ledgers (worked-example part) mirror the two Lean
    evidence bundles theorem-for-theorem and serve as the human-readable index into the
    dependency graph.
- **`staging_rp2/`** — staging Lean files; not cited by the paper.
- **`focal_closure.py`** — exact harmonic cancellation at the zeros, demonstrated by the
  focal-closure growth locator: the finite 3D bank (lanes P/M/U riding the carrier) locates its
  own vanishings as lane-balance events, with no L-function call in the loop (published reference
  ordinates enter only the final `|diff|` validation column). Families: `eta`/ζ, real and complex
  Dirichlet characters, Ramanujan Δ, and elliptic curve 11.a.
  - Run: `python3 focal_closure.py test` (~30 s) or `python3 focal_closure.py demo` (~2–4 min).
- **`carrier_fiber/`** — the finite Python carrier/fiber harness: native `π/3` carrier scan,
  harmonic pencil marker, and cumulative carrier-clock validation, kept separate. `validate`
  runs finite-first; the mpmath analytic certificate is opt-in via `--mode analytic`.
  - Run: `python3 carrier_fiber.py test` from `carrier_fiber/`.
- **`phasor_explorer/`** — interactive HTML explorer for the phasor bank (`explorer_v2.html`).
- **`FIBER_DYNAMICS.md`** — the fiber-dynamics research record (reverb/residues, the GUE
  resolution, the arithmetic medium, exact phase quantization, and the associated Lean ledger).
- **`paper/`** — the earlier standalone paper (`helix_phasor_model.tex`), superseded by
  `automorph/universal.tex`; retained as an archive.
- **`tmp/`** — working files and one-off computations referenced by the reproducibility
  appendix.

## Where to start

Read the paper's Introduction for the thesis and the seven-result map, then the worked-example
part (**"Worked Example: Two Conditional Proofs of GRH"**): it builds the basic configuration
from scratch — state space, carrier, fiber, the bidirectional 3D↔1D transport, `z = e^y` — states
the two decisions and the decision matrix, and exercises every mechanism the rest of the paper
generalizes. The empirical scripts and controls live in the reproducibility appendix; the proof
text consumes theorems only.

## Correspondence discipline

The paper cites Lean declarations by name in parentheses throughout (e.g.
`vonNeumannOp_isSymmetric`, `gramH_rank_drop_iff_L_zero`); the Python instruments mirror the
same definitions, each annotated with its Lean identifier. Claims are held to three registers,
never blended: **proven** (Lean, standard footprint), **measured** (calibration and independent
reproduction, never proof), and **decided** (the two named readings, the community's).

## Author

Samuel Lavery — sam.lavery@gmail.com
