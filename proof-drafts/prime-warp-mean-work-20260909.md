# Growing prime-warp integral: construction

The previous goal turn made verified progress on the logarithmic coordinate layer,
and its compiler failures direct this turn to the growing bank upstream. The RH target
is unchanged. No unconditional RH declaration has been produced.

The next analytic component is the actual growing strain

    q_c(t) = -(1/pi) sum_n max(1 - log(n)/(c log(max(t,2))), 0)
                         * Lambda(n)/(sqrt(n) log(n)) * sin(t log(n)),

where 0 < c < 1 and the sum is finite at every height. This is
`registryStrain c` after unfolding `registryStrain`, `warpStrain`, `rieszStrain`,
`rieszProfile`, `strainClock`, and `logScale`.

The component to construct is |integral_0^T q_c(t) dt| = O(T^c + 1), hence o(T).
This controls the prime contribution to the desired lower bound. It does not identify
the native residual `Smult - q_c` with zero.

Without a prior expectation, I would exploit the bounded primitive of each clock
before taking absolute values of the growing sum.

Strategy A: integrate a weighted sine clock by parts. The primitive of sin(omega*t)
is -cos(omega*t)/omega. The Riesz weight grows from 0 to at most 1, so its total
variation contributes at most 1, independently of the interval's length.
First Lean line: `have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul ...`.

Strategy B: express a monotone weight as a positive layer integral of indicators of
terminal intervals, then use the unweighted sine primitive on each interval.
First Lean line: `rw [MeasureTheory.integral_integral_swap]` after establishing the
layer representation and integrability. Search found integration by parts available;
strategy A is being constructed first.

Search commands run:

```sh
rg -n '(rieszStrain|registryStrain|warpStrain).*(integral|[Mm]ean|[Ss]ublinear)|integral.*(rieszStrain|registryStrain|warpStrain)|prime.*[Mm]ean|[Ss]train.*[Mm]ean' RequestProject --glob '*.lean'
rg -n 'integral.*sin.*mul|integral_sin|integral_comp_mul_right|integral_finset_sum' .lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Integrals .lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral --glob '*.lean'
rg -n 'second.*[Mm]ean|[Mm]ean.*second|Bonnet|Stieltjes.*integral|integral.*Stieltjes|integral.*[Vv]ariation|[Vv]ariation.*integral' .lake/packages/mathlib/Mathlib --glob '*.lean'
```

Semantic searches: LeanSearch `bound integral monotone weight times sine integration
by parts`; Loogle `"integral_deriv_mul_eq_sub_of_hasDerivAt"`.

## Verification and scope

`PrimeWarpOscillation.lean` now proves the weighted-clock estimate, the active
logarithmic weight estimate, and the estimate including admission at `exp(omega/c)`.
The final source passed the targeted build, with standard axiom output:

```text
Build completed successfully (8697 jobs).
```

The wrapper `RegistrationPrimeMean.lean` keeps the time-dependent weights inside the
integral when taking a common finite summation range. Its first compiler run verified
the individual prime-clock bound and found one scalar floor-bound mismatch in the
sum estimate. That mismatch was repaired, and the subsequent run also checks the
new little-o conclusion.

The auxiliary `registryStrain` front is `c * log(max(t,2))`. It is not the carrier's
`log(physicalHead t)` front. The latter must be treated together with the end and
archimedean terms of its explicit formula; no transfer of the auxiliary little-o
bound to that front is asserted.

For the actual carrier, a search for `Nindex`/`physicalHead` derivatives and monotonicity
found no direct declarations. A second search for the underlying arclength located
`Geometry.arclength_hasDerivAt` and `Geometry.arclength_strictMono` in `AreaLaw.lean`.
Unfolding the carrier gives

    physicalHead(t) = (3/pi) arclength(1,3,exp(t)),
    physicalHead'(t) = (3/pi) speed(1,3,exp(t)) exp(t),
    (log physicalHead)'(t) = physicalHead'(t) / physicalHead(t).

These derivative and monotonicity statements are written in `CarrierHeadRegularity.lean`.
They use the actual carrier definition and do not assert a registration or zero-location
conclusion.
