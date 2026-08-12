# Helix–Frobenius — working rules

## Ground rules (Sam, 2026-07-08) — non-negotiable

1. **Everything is to be proven unconditionally.** No conditional results, no
   "assuming X". If a step needs an unproven input, it is not done — name the gap,
   do not paper over it.
2. **Use the Edit tool, not scripts, to make changes.** Do not write throwaway
   Python/shell scripts to mutate the paper or the Lean sources. Edit files directly
   and surgically with the Edit tool.
3. **Sam approves everything.** From 2026-07-08 forward, get explicit approval before
   any edit or state-changing action. Propose the change, wait for the go-ahead.
4. **This is a 3D system.** The helix is in 3D; everything is proven in 3D. The 1D
   L-function is the projected readout, and 1D analogs of 3D facts are real and useful
   — the functional equation, local factors, root number, etc. all have legitimate 1D
   readouts. What is **forbidden** is raising something that only matters in the chart
   readout as an *obstruction* to a 3D result. The convergence abscissa "Re s > 1" is
   where the projected series stops converging — a chart artifact, not a barrier on the
   carrier: the fiber's phasors start at height 0 and grow continuously, with no
   convergence gate in 3D. Never import a projection-chart artifact as an obstruction.
5. **Novelty-first; think 3D helix geometry first, in all cases.** (Sam, 2026-07-29)
   A novel idea that solves the problem is used **in place of** the old idea — replace,
   don't defer. Novelty is OK: it is how we solve math problems here. The subject is
   algebraic topology (or similar) of the 3D helix, and that geometry is the first
   frame reached for on every problem — never something to be set aside in favor of
   traditional 1D approaches. Ever.
6. **"Open frontier" claims require extensive research; no RH/GRH disclaimers.**
   (Sam, 2026-07-29) Never label anything "open" / "frontier" / "undischarged" without
   extensive research showing it is not already proven in this repo — read the corpus
   at source, cite what was checked. This codebase has repeatedly mislabeled compiled
   results as open (see the correction ledger). When file-scoped honesty is all you
   have, write "not proven in this file" and nothing broader. And do not write "does
   not assume or prove RH/GRH" (or any variant) in docstrings or prose — it reads as
   paranoia, not accuracy. Results speak in their own scope. (Amends the tone-policy
   scope-line note below.)

7. **Harmonics is a required field, not a disposition.** (Sam, 2026-08-04)
   Rule 5 states the disposition and it is not enough: dispositions lose to local
   retrieval priority at every hard step, because the classical tool always has the
   higher prior. So harmonics is made *checkable*, like the register:
   - **⟨1⟩ Every bound or estimate carries a harmonic-content line** — the object's
     own scale (never unit 1), its DC/AC split, and whether the difficulty is on the
     carrier or in the chart. A missing line is a defect of the same class as a
     blended register. If the line cannot be filled, the bound is not ready.
   - **⟨2⟩ DC first, always.** No estimate before the common mode is *evaluated
     exactly*. Every result that has landed here has the shape: find the common mode,
     compute it outright, estimate only the remainder. Estimating something that has
     a computable common mode is the recurring failure.
   - **⟨3⟩ Retrieve, don't reconstruct.** The harmonic dictionary is kept in memory
     (`harmonic-first-discipline`) and consulted; reconstruction is what fails under
     pressure.
   **The alarm:** *if I am doing worst-case analysis, I have already dropped
   harmonics.* Harmonic analysis computes the typical structure exactly and books the
   exception; worst-case analysis abandons the structure and bounds an enemy. Lattice
   first minima and twin primes are both worst-case objects, and both were drops
   (2026-08-04, caught by Sam twice in one session).
   **Format:** every response opens and closes with a one-line ⟨1⟩⟨2⟩⟨3⟩ blurb —
   the top line a *pre-commit* (what is about to be done), the bottom line an *audit*
   (what was actually done). Pre-registration then measurement, the house discipline
   applied to my own reasoning.

8. **Novel-vs-classical ratio is declared and audited, every turn.** (Sam, 2026-08-04)
   Rule 7 made harmonics checkable; this makes *the kit itself* checkable, because the
   failure mode survived rule 7: on Erdős #1095 I reached straight for additive characters
   and a Dirichlet kernel, died at the joint modulus, and only then discovered the window
   was a chart artifact that cell collapse dissolves. The instrument being in the file is
   not retrieval — using it is.
   - **Top of every response:** a declared percentage of *novel* (house/MDHNT) technique
     versus *classical*, naming the specific instruments to be attempted.
   - **Bottom of every response:** a breakdown of which novel instruments actually fired,
     how each was applied, and what it contributed toward resolving the proof — including
     the ones that were planned and never reached.
   This sits alongside the ⟨1⟩⟨2⟩⟨3⟩ blurbs of rule 7, which stay.

The active proof lives in `automorph/universal.tex`.

## Prove what is true; "GRH-strength" is not a stop sign

We are here to prove things that are true, to be true. The classification test for any lemma
or idea is exactly two questions:

1. Does it **assume** GRH/RH?
2. Is it **circular** (defined via its own conclusion)?

If the answer to both is no, it is a valid target and worth at least the attempt — **regardless
of how strong it is**. The labels "GRH-equivalent" / "RH-strength" act as thought-terminators:
they must never end an investigation on their own. We work in 3D space, where the classical
"big open problems" attached to GRH/RH are not even properly defined, so the potential notion
that something might actually prove GRH/RH is not a reason to refuse to consider it. Chances
are the idea is wrong anyway — but you will never find out unless you stare at it and evaluate
it on its merits. If it's true, it's true; it's just math.

(Corollary of honesty, unchanged: never *claim* more than what is proved — isolate any
unproven RH-strength step as an explicit named hypothesis, as the codebase already does — but
isolating a hypothesis is the *output* of an attempt, not a substitute for making one.)

## Tone policy (adopted 2026-07-02, Sam's confirmation)

The paper and prose take the **evidence-weighing stance**, not neutrality-as-silence.
Sandbagging is miscalibration too. Three tiers, never blended:
1. **Results** — exactly as strong as proved/measured; Lean statements carry no tone.
   (Reflexive "does not assume or prove RH/GRH" scope lines retired 2026-07-29 by
   ground rule 6.)
2. **State of the evidence** — explicitly weigh it: the working hypothesis best supported is
   that **every zero has a source** (`EveryZeroHasSource` = GRH; "projection primacy" retired
   2026-07-01 — the negation is a *sourceless zero*, an unknown of the 1D limit, not a defect
   of the 3D representation), presented as the favored branch of the dichotomy, grounded in
   the tagged evidence (`FIBER_DYNAMICS.md`), never forcefully asserted.
3. **Falsifiability register** — pre-commit in print to what disconfirmation looks like
   (non-collapsing arch floor / non-Euler spectral line / phase cell ≠ π in the fiber's clock /
   weight-law violation / configuration-universality break) and publish any hit as prominently
   as confirmations. Current count after deliberate searching: zero. Retractions stay in the
   record (growth-clock, ghost lines) — they prove the falsification machinery runs.

## Ontology

- **1D = the Dirichlet L-function** (analytic object). **3D = the phasor representation**
  (the bank on the carrier). There is no "1D phasor representation" — the 1D series is the
  readout/projection of the 3D bank.
- L-function values are for **final readout verification only** — never inside a locator,
  a pencil definition, or a validation default.
- The π/3 structure's claim is **exact harmonic cancellation at the zeros** (residue-free
  vanishing; P = M lane balance; exact ℤ[ζ₆] μ6 closure), not "finds zeros everywhere".
- The strip / Abel summation is a 1D-projection device with no 3D counterpart. The bank lives
  at heights > 0; each phasor enters continuously at zero magnitude and grows until finished.

## Build & test

- Lean: `lake build` (Mathlib v4.31.0, cached; ~8600 jobs). Axiom footprint of every named
  theorem must stay `{propext, Classical.choice, Quot.sound}`; no `sorry`/`axiom`.
- Python: `python3 focal_closure.py test` (canonical 3D locator + exactness tests),
  `python3 carrier_fiber.py test` from `carrier_fiber/` (harness; `validate` is finite-first).
