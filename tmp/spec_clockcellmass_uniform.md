# Refutation spec: uniform per-cell absolute mass of S(t) in clock measure

Self-contained. No repository context required.

## The claim, as a falsifiable proposition

Let ζ be the Riemann zeta function. Define, for t > 0 not an ordinate of a
zero:

* S(t) = (1/π)·arg ζ(1/2 + it), with the argument obtained by continuous
  variation along the path from 2 (on the real axis) up to 2 + it and then
  horizontally to 1/2 + it (the standard convention; S jumps by the zero
  multiplicity at ordinates).
* θ(t) = the Riemann–Siegel theta function, θ'(t) ≈ (1/2)·log(t/2π).

Partition heights into consecutive "π-cells": fix c_0 = 100 and let
c_{n+1} be defined by θ(c_{n+1}) − θ(c_n) = π.

**CLAIM (to be tested): there is a single constant C such that for every
cell n: M_n := ∫_{c_n}^{c_{n+1}} |S(t)|·(θ'(t)/π) dt ≤ C.**

(Equivalently: the per-cell absolute mass of S in the measure dθ/π is
uniformly bounded over all cells.)

## Inputs

* Any standard multiprecision library with ζ and θ (e.g. mpmath:
  `mp.zeta`, `mp.siegeltheta`, `mp.nzeros`/`mp.zetazero` for branch
  checks).
* Branch tracking for arg ζ: integrate arg continuously along the two-leg
  path, or equivalently compute S(t) = N(t) − 1 − θ(t)/π with N(t) from a
  zero counter; cross-check the two methods on 100 random points
  (disagreement > 10⁻⁶ voids the run).

## Procedure

1. For each batch B_k, k = 2..6: heights starting at 10^k, take the first
   5000 consecutive π-cells.
2. In each cell compute M_n by adaptive quadrature of |S(t)|·θ'(t)/π
   (subdivide at the zero ordinates inside the cell; S is piecewise smooth
   between consecutive ordinates).
3. Record per batch: max_n M_n, mean_n M_n, and the count of cells with
   M_n > 2.

## Decision rule (pre-registered)

* If max_n M_n over batch B_6 exceeds 3× the max over batch B_2, and the
  batch maxima are non-decreasing in k (allowing one inversion), the CLAIM
  is REFUTED-IN-TREND: the uniform constant does not exist.
* If the batch maxima of B_5 and B_6 agree within 20% and neither exceeds
  2× the B_2 maximum, the run SUPPORTS uniform boundedness at accessible
  heights (this does not prove the claim; it constrains it).
* Any other outcome: INCONCLUSIVE; report the numbers.

## Prediction (stated before any run)

I predict REFUTED-IN-TREND: batch maxima and means grow slowly with k,
consistent with the local average of |S| growing like a power of
log log t (Selberg-moment behavior), while remaining numerically small
(max M_n < 5 at 10^6). Reason for the prediction: the second moment of S
on [T, 2T] is asymptotically (1/2π²)·T·log log T, so per-cell averages of
|S| against the ≈π-normalized clock measure inherit a (log log)^{1/2}
drift; heights up to 10^6 probe log log ≈ 2.6, so the drift is weak but
should be visible in the batch means.

## Why this matters (context for the router, not the executor)

A positive constant C for all cells is the hypothesis form consumed by a
compiled reduction; if the trend refutes it, the reduction's mass input
must be weakened to an averaged form for ANY cell choice, which redirects
a formalization program. The signed analogue (cell integrals of S·θ'/π
without absolute value) is known to behave much better; the absolute-value
question is the one this spec decides.
