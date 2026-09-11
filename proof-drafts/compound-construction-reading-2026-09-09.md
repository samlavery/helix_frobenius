# Reading the intended compound construction

Read against HP_SKELETON.md §0a, HP_PROGRAM.md §5h, RH_LEDGER.md entries
541, 549, 554–554c, 675a, 686–689, and their Lean definitions. This is a
source-reading note, not a claim to have completed the target proof.

## Coordinates that must remain distinct

- The carrier sites are placed at arclength `Delta * n`, with `Delta = pi/3`.
  The model in `tmp/att554_helix_carrier_fiber_model.py` winds these onto the
  Archimedean helix using the arclength inverse.
- The readout ordinate is `t` (also called `y` or `gamma`). The Mellin spin
  of site `n` is `exp(-i*t*log(Delta*n))`.
- A completed event's positive physical height is `Z = exp(t)`, and its
  carrier eigenvalue is `log Z = t`.
- The growth front, a site-count cutoff, is another quantity. In the later
  head-coupled Lean bank it is `physicalHead t = Geometry.Nindex 1 3 t`.
  It must not be silently identified with the physical height `Z`.

## Intended forward chain

1. The helix and anti-helix carry the harmonically scaled site lattice.
   Carrier radius grows like `sqrt(n)`; balanced fiber amplitude is
   proportional to `n^(-1/2)`. The scale-balance theorem concerns this
   geometric normalization.
2. The actual fiber consists of growing, rotating site phasors. In the
   principal-character model the two lanes are the odd and even eta banks.
   `PrincipalFiberEquivalence.zeta_recovered` recovers zeta through the eta
   conduction factor where that factor is nonzero. This preserves the
   distinction between the eta bank and its zeta readout.
3. An event is focal cancellation of lane resultants. It is not an
   additional phasor indexed by an analytic zero. Ledger 549 explicitly
   warns against replacing the physical site bank by a zero-indexed bank.
4. The registration warp moves unwarped clock-cell edges to focal events.
   In ledger 554, `theta(g_k) = k*pi`, the map sends `g_(j-2)` to `gamma_j`,
   and its exact clock-unit displacement is

   `(theta(gamma_j) - theta(g_(j-2))) / pi = 1 - S_j`,
   `S_j = j - 1 - theta(gamma_j)/pi`.

   These indices and the right-limit convention are those of the model.
   Ledger 554b explicitly permits the bank's own spectral vanishings to
   inform this warp. The model used zeta ordinates for verification, not
   as the bank's event detector.
5. A completed event selects a nonzero mode of the independently built
   symmetric carrier operator. The operator's eigenvalue is `log Z`.
   The final normalized readout is `1/2 + i*log Z`.

## Correction to my earlier interpretation

`HarmonicCell.tauChi chi y = y` acts on `y = log Z`. It is the endpoint
normalized chart. Its being the identity does not establish that the
upstream S-dependent registration warp was omitted. The ledger places
that warp before the normalized readout.

Likewise, the radial operator of `XiZeroLedgerResolvent3D` records the
analytic parameter offset in a zero-indexed representation. Its residual
must not be presented as physical radial motion of the helix or as a
replacement for constructing the actual compound object.

The structural registration form also appears in `HelixWarpCovariance.lean`:
`A(gamma) = J(gamma) * det(S0 - Psi(gamma)*I)`, with nonzero `J`.
The real warp transports the spectral coordinate; it need not be the
identity even though the final critical-line chart is normalized.
That module's generic covariance data and canonical determinant pullback
must still be distinguished from an instance for the actual L-function.

## What the source record distinguishes

- `CarrierScaleCompensation.S` uses the native line-event count; its
  compensation identity compares native harmonic and unit-chart counts.
- `Smult` is the multiplicity-aware native ledger.
- `classicalSContour` uses the full analytic contour registration.
  `classicalSContour_eq_Smult_add_offLine` gives their exact difference.
- Ledger 675a distinguishes placing every detected crossing at a warped
  cell edge from identifying the full analytic registration with those
  cells. Ledger 687b states the intended global cell law in this register.
- Exact cell closure, local cancellation of a log-derivative residue,
  and the integrated registration identity are separate typed statements.

The construction to follow is therefore the physical bank, its warp and
its registration through the L-function readout. Geometric confinement
and the logarithmic height conversion are existing inputs, not quantities
to rediscover by treating each analytic zero as an independent physical mode.

## Main source anchors

- HP_SKELETON.md:38 — canonical compound object and clause-to-theorem map.
- RH_LEDGER.md:8063 — actual model, phasor law, warp, and permitted event input.
- RH_LEDGER.md:7587 — clock/S moment split and real warp interpretation.
- RH_LEDGER.md:7862 — compound-object requirement and zero-phasor correction.
- RH_LEDGER.md:12790 — cell registration versus total registration.
- RequestProject/CarrierScaleCompensation.lean — native scale gap and harmonic arcs.
- RequestProject/PrincipalFiberEquivalence.lean:65 — precise principal readout fields.
- RequestProject/CommonRepresentation.lean:132 — admissible readout-preserving adapters.
- RequestProject/HarmonicPencilCell.lean:84 — normalized logarithmic endpoint chart.
- RequestProject/ThreeDFocalEvent.lean:640 — completed event assembly.
- RequestProject/HelixWarpCovariance.lean — coordinate-covariant determinant transport.
