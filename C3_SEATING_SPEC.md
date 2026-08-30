# C3 SEATING-BOX SPEC (pre-registered, 2026-08-28)

The count-register certificate for Road C3, drafted per the register law: the
sign flips at every zero because a zero IS a harmonic vanishing event — the
flip is the chart's record of the completion.  So the terminal certificate is
an integer equality per box (tally of completions = strip census), not a
pointwise inequality.  This spec pre-registers the event definition, the box
partition, the decision rule, and the prediction — before the probe runs.

## The three compiled counters (the ledger's layers)

L1. **Bank tally** `F(box)`: sign flips of the despun readout — the
    gauge-aligned real projection `Z(t) = e^{iθ(t)}·(readout at ½+it)`, with
    `θ = CarrierScale.theta` (compiled clock; classical identification
    compiled at `StExplicitBridge` Rung A).  Computable from the bank's own
    sums (theta identity / Riemann–Siegel form); **no zero location is an
    input**.  A flip is a completion event's chart record.
L2. **On-line census** `zeroEventCount` (compiled,
    `CarrierScaleCompensation.lean:663`): distinct on-line ordinates, no
    multiplicity.
L3. **Strip census** `stripZeroCountMult` (compiled, RvM chain,
    `DVPThetaAsymptotic.lean`): all strip zeros with multiplicity, by the
    argument principle / contour side.

Always `F ≤ L2 ≤ L3` boxwise (flips see odd multiplicity as one; the strip
contains the line).  **The seating box identity — the C3 target — is the outer
equality per box:**

    F(box) = stripZeroCountMult(box)        for every clock box.

Equality forces: every strip zero on the line, simple, and flip-visible.  This
is RH-strength content in count form (EQUIV is expected and is not a defect —
rule 11 guard: the constructive burden C3 carries is the *exhibited tally
machinery*, discharged by identity per box, not by estimate).

## The boxes

Clock cells: box boundaries at the compiled clock's ticks `θ(g_k) = (k−1)·π`
(Gram-type points of the tree's own `theta`).  Native because the compiled
`count_decomposition` reads `N = 1 + θ/π + S` — per clock cell the DC count is
exactly 1 and `S` is the defect ledger.  Windowed stage supply
(`ZetaPhaseBridge.exact_stage_in_window`) guarantees the cell structure is
uniformly available past the compiled threshold.

## The numeric probe (control), pre-registered

* Range: ordinates `0 < t ≤ 400` (matches the adjudicator's tested range).
* `F`: sign flips of Hardy `Z` on a grid of step `0.02` per cell with
  bisection refinement to `1e-9`; flips only (no zero locations retained).
* `L3` per cell: independent counter `mpmath.mp.nzeros` at cell boundaries
  (argument-principle implementation, not zero lists).
* **Decision rule (registered before running):**
  - PASS-box: `F = ΔN` for the cell.
  - PAIR-box: `F` deficit in one cell compensated in an adjacent cell with the
    two-cell sum exact (Gram's-law violation pattern) — counts as PASS for the
    seating identity at the two-cell resolution; recorded.
  - DEFECT: any window of ≥ 3 consecutive cells where the summed tally is
    strictly less than the summed census — this is the outcome that would
    *refute* the flip-visible form of the certificate at these heights.
  - INSTRUMENT-FAIL: `F > ΔN` anywhere (impossible if both counters are sane).
* **Prediction (registered):** all boxes PASS or PAIR below `t = 400`; first
  PAIR activity at the first Gram-law violation (`g₁₂₆`, `t ≈ 282.45`); zero
  DEFECT windows (known Rosser exceptions lie far above this range).

## The Lean target shape this feeds

`seating_box : ∀ k ≥ k₀, bankTally k = stripZeroCountMult (cell k)` with
`bankTally` defined from despun sign data (L1).  Compiled ingredients ready:
the clock and its classical identification (Rung A), `count_decomposition`,
`StClockJumpLaw`, the S-explicit packet bridge, the argument-principle count,
windowed stage supply, and the hypothesis-free closure machinery.  The open
mathematics is exactly the outer equality; nothing else in the chain is
hypothetical.

## Register discipline

Nothing in this spec bounds `S(t)`; the defect ledger is *recorded*, not
estimated (2026-08-12 law).  The probe's failure mode is pre-registered as
data, not as an obstruction: a DEFECT window, if found, localizes where the
certificate must carry pairing/multiplicity structure — it does not terminate
the route.
