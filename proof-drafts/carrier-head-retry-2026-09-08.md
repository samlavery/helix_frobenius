# Carrier-head retry, 2026-09-08

## Fixed target and definitions

The unconditional target remains `CriticalLinePhasor.DVP.SmultIntegralSublinear`.
Unfolded in ordinary mathematics, for every positive ε, there is a threshold B such that
for every real T ≥ B,

    -ε T ≤ ∫₀ᵀ (N_on(t) - 1 - θ(t)/π) dt.

Here `N_on = zeroEventCountMult` counts on-line zeros with multiplicity. The full ledger is
`SAll(t) = Smult(t) + offLineStripZeroCountMult(t)`.

For the carrier route, the unit-gauge head is the existing
`Geometry.Nindex 1 3 y = (3/π) ∫₀^(exp y) sqrt(10 + (6πt)²) dt`.
The new `CarrierHeadFiniteFiber.lean` uses that head and the smooth profile
`w(u) = exp(1 - 1/(1-u²))` for `u < 1`, zero otherwise. The finite bank sums the positive
integer sites below the head, with alternating signs and factors `exp(-s log n)`.
Each entire function holds the carrier head fixed while varying the complex readout `s`.

## Compiled construction

`lake env lean RequestProject/CarrierHeadFiniteFiber.lean` exited 0.

* `physicalHead_lower`: `9 * (exp y)^2 ≤ physicalHead y`.
* `physicalHead_gt_height`: `0 ≤ y → y < physicalHead y`.
* `physicalHead_tendsto`: the carrier head tends to infinity.
* `carrierHeadFiber_entire`: each fixed carrier-head bank is entire.
* `finiteFiber_conj`: conjugation commutes with the bank readout.

All five printed axiom footprints are `[propext, Classical.choice, Quot.sound]`.
The new source has no matches for `axiom |sorry|admit|@\[implemented_by\]`.
No existing theorem signatures were modified.

## Actual proof attempts

Question used for the decomposition: what follows from the actual definitions and the compiled
inequalities, without predicting the outcome?

A. Use the compiled registered displacement to obtain a horizontal displacement sign.
First Lean line: `have hregistered := growth_direction_re_neg hρ h0 hsimple hγ`.
File: `/tmp/carrier_retry_phase.lean`; compiler log: `/tmp/carrier_retry_phase.log`.
After expanding the real part, `linarith`, `nlinarith`, and `exact?` did not discharge
`(etaTrivial (ρ - 2) / deriv etaTrivial ρ).re < 0`.
The existing inequality includes multiplication by `conj (deriv riemannZeta ρ)`.
This attempt does not establish a finite-head zero-location theorem.

B. Apply Littlewood's established little-o estimate before splitting the on-line ledger.
First Lean line: `have hsmall := littlewood_o_input_holds.bound (show 0 < ε / 2 by positivity)`.
File: `/tmp/carrier_retry_mean.lean`; compiler log: `/tmp/carrier_retry_mean.log`.
This gives `|∫₀ᵀ SAll| ≤ (ε/2) T` eventually. The non-negative off-line integral is then
subtracted using `integral_smult_split`. The target lower bound is not discharged by
`linarith`, `nlinarith`, or `exact?`.

C. Return to the parent average target through the existing cell-telescoping theorem.
First Lean line: `apply CriticalLinePhasor.ContourArgument.integral_sublinear_of_boundary_and_cell`.
File: `/tmp/carrier_retry_cells.lean`; compiler log: `/tmp/carrier_retry_cells.log`.
The selected test cells have boundaries `c(n) = n + 10` in readout height; these are not a
new definition of carrier sites. The remaining goals are boundary integral sublinearity
and single-cell absolute-mass sublinearity. No proof of either is added as an assumption.

The RH discharge is not complete. The new source certifies the head geometry and finite-bank
analytic structure; it does not claim zero-freeness or the averaged lower bound.

## Search record

Commands run from the project root included:

```sh
rg -n 'SmultIntegralSublinear|smultIntegralSublinear|smult_integral_sublinear|integral.*Smult|Smult.*integral|band.*[Nn]onzero|[Nn]onzero.*band|band.*zero|zero.*band' RequestProject -g '*.lean' -g '!DVPStation*'
rg -n 'Nindex|carrierWarp|carrier_warp|warp.*Nindex' RequestProject -g '*.lean'
rg -n 'finite.*[Ff]iber|smooth.*[Ww]indow|entryWindow|exp \(1 - 1 /|exp \(1 - \(1|headAdapt|head_adapt' RequestProject -g '*.lean'
rg -n -i 'growth_direction|displacement.*re|re.*displacement|eta.*deriv.*neg|negative.*direction|direction.*negative|smult.*lower|lower.*smult|smult.*sublinear|sublinear.*smult' RequestProject -g '*.lean'
rg -n -i 'smultIntegralSublinear|smult_integral_sublinear|integral.*smult|smult.*integral|smoothEntry|smooth_entry|entryWindow|entry_window|headAdapted|head_adapted' .lake/packages/mathlib/Mathlib -g '*.lean'
```

Semantic searches used `lean_leansearch` for locally uniform zero-free limits and real parts
of complex quotients, and `lean_loogle` for `TendstoLocallyUniformlyOn` and `Complex.div_re`.
The repo's `LimitDominance.lean`, `PhaseBound.lean`, `LittlewoodRegisterDoor.lean`, and
`HarmonizedCellTelescoping.lean` supplied the relevant interfaces inspected in this retry.
