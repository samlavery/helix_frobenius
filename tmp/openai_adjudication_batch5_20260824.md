# OpenAI adjudication — C3 Batch 5 — 2026-08-24

No commit.  `tmp/att542_out_floor60.txt` is inadmissible: it was produced by a Claude
rerun that violated the explicit execution limit.

## Chart dictionary

- Native helix: `Re s > 0`; entry wall `Re s = 0`.
- Xi chart: `z = i(s - 1/2)`, so `Re z = -Im s` and `Im z = Re s - 1/2`.
- Conjugation transports to `s ↦ 1 - conj s`; `E` and `E*` are the helix/anti-helix pair.
- Carrier chart: physical height `Z`, analytic ordinate `t = log Z`.
- Native harmonized readout: `N_pi3 (exp t)`.  Unit-1 receiver:
  `R_1 (exp t) = 1 + theta(t)/pi`.
- Registration gap: `S(t) = N_pi3(exp t) - R_1(exp t)`.  Unit 1 is the comparison
  receiver, not the native carrier.
- The carrier-scale `S(t)`, Xi-chart `z`, and Hermitian pencil `S_t` are distinct.

## COMPILED

All declarations below were independently checked with `lake env lean`; every printed
footprint is exactly `[propext, Classical.choice, Quot.sound]`; escape-hatch scan clean.

- `RequestProject/XiHelixChart.lean`: twelve chart/inverse/reflection declarations.
- `RequestProject/XiStructureResidual634.lean`: four declarations; wording corrected
  from “low strip” to “bounded ordinate band”; theorem statements unchanged.
- `tmp/SChartAudit.lean`: `readout_exp`, native/unit identifications, carrier-scale
  compensation, and the three `Sgap` cocycle laws audited.
- `tmp/c3b5_A1.lean` (11 declarations): compiled even-kernel elimination, exact theta
  pair change-of-variables algebra, bracket identities, and scalar quadratic thresholds.
- `tmp/c3b5_A2.lean` (11 declarations): the abstract radial identity and its explicit
  hypotheses, head-dominates-tail summation lemmas, hyperbola weight, and divisor-phase
  bounds.
- `tmp/c3b5_A3.lean` (8 declarations): abstract logarithmic-derivative comparison,
  Liouville normal-form algebra, Riccati derivative identity, and positive-potential
  threshold.  These are conditional consumers; no theorem here supplies the required
  Bessel derivative bound.
- `tmp/c3b5_A4.lean` (7 declarations): two exact PSD obstructions, an explicit negative
  Hankel minor, and even-convex monotonicity.  Independently compiled after Claude was
  interrupted.
- Batch 4 survivor: `U(s) = ∫_s^∞ T(r)dr = ∫_s^∞ (u-s)^2 C(u,x)/2 du`, and uniform
  `U(s) ≥ 0` implies the required sinh pairing, under the stated Fubini/integrability
  hypotheses (`tmp/c3b4_A2.lean`, `tmp/c3b4_A4.lean`).

## OPEN

Smallest current analytic leaf:

`∀ x s, 0 ≤ s → 0 ≤ U_x(s)`, where

`U_x(s) = ∫_s^∞ (u-s)^2 C(u,x)/2 du`.

Constructive subleaves now exposed:

1. Full theta-mode identity: justify the sum/integral interchange for every `(n,m)` and
   retain all cross terms.
2. Eventual sign route: prove an explicit full-sum remainder bound after isolating the
   `(1,1)` mode; finite truncations do not supply this.
3. Radial route: discharge the actual inequality on the logarithmic derivative of
   `K_{i x}` needed by `C3B5.A2.radial_pos`; positivity of `K_{i x}` alone is insufficient.
4. Compact window: prove quadratic-ramp positivity on the remaining bounded interval.

## EQUIV

- `XiStructure.rh_iff_xiStructure_dominates` navigates between the target theorem and
  upper-half-plane domination by the structure function.
- `rh_iff_shallow_channel_dominates_634` isolates the high-ordinate shallow-depth seat
  channel after the compiled 634 ordinate band and deep channel.
- The C3 transform and weighted-tail identities navigate from vertical Xi monotonicity to
  the quadratic-ramp leaf above.

## FAILED

- Uniform linear-ramp positivity: `T(0,60) = -2.4411414711711282366e-36`.
- Fixed-`d` J-kernel fiber positivity does not control the outer `cos(xd)` integral.
- The `(1,1)` Macdonald mode does not transfer its zero count or sign by itself to the
  complete theta double sum.
- Direct PSD factorization with `rampKernel(a+b) = max(a+b,0)^2` fails by the compiled
  two-point minor in `tmp/c3b5_A4.lean`.
- Generic Hankel-square factorization fails by the compiled negative minor for the tested
  exact model in `tmp/c3b5_A4.lean`.
- The accidentally rerun `att542` output is excluded and supports no claim.

## Next literal Lean step

Instantiate `C3B5.A3.logDeriv_le_one` with a formal `z(A) = sqrt(A) * K_{i x}(A)` only
after importing or proving a differentiable real-valued definition of `K_{i x}` and its
modified-Bessel ODE.  The next theorem must conclude the derivative bound rather than
accept it as a hypothesis; then compose it with `C3B5.A2.radial_pos_of_ge_eight`.
