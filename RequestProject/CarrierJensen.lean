import RequestProject.CarrierScaleCompensation
import RequestProject.ZeroCountJensen

/-!
# Carrier Jensen: the Tier-2 interface and increment structure

`CarrierScaleCompensation.lean` proves the ledger identity `S t = zeroEventCount t − 1 − θ(t)/π`
(the on-line census against the Γ-clock).  This file states the Tier-2 target — the carrier
Jensen bound: the defect between the census and the clock never exceeds a bounded number of
window budgets — in its two equivalent registers, and proves the increment structure the
eventual analytic brick will consume.

* `S_increment` (proven): the defect increment over any window is exactly the census increment
  minus the clock advance — the "gap count between crossing events measured against the winding
  clock" in identity form.
* `S_ledger_bound` (proven): the trivial two-ledger bound, `|S| ≤ census + 1 + |θ|/π`.
* `zeroEventCount_le_xiZeros_ball` and `census_polynomial_bound` (proven): the census disk wire —
  every on-line event embeds as a ξ-zero in the origin ball, so the compiled Jensen count
  `ZD.ZeroCount.xi_zero_count_disk_bound` caps the line census by `C·(t+1)·log(t+1)`,
  unconditionally.  The first compiled growth bound on the line census.
* `CarrierJensenClockBound` / `CarrierJensenBound` (named targets) — see the register note below.
  Neither target is asserted; the types pin them.

## The two directions are not two halves of one analytic bound

Both named targets are `|S t|` bounds, hence two-sided; but the two directions are **not**
symmetric halves of a single analytic estimate, and reading them that way misfiles the harder
one.  Backlund's classical bound `|S_class| ≤ A + B·log t` *is* symmetric — one argument gives
both directions.  The asymmetry appears only on passing to this file's `S`, which counts on-line
**events** (`zeroEventCount`) while still measuring against the unit-chart clock `ϑ/π`.  That is
a cross-register construction by design: `carrier_scale_compensation_S` states it outright as
`N_{π/3}(eᵗ) − N_1(eᵗ) = S t`, native count minus *unit*-chart registration, and §7 of
`CarrierScaleCompensation.lean` proves the general two-scale gap `Sgap H K` is a coboundary of
the per-scale potential `NH` (`Sgap_refl`, `Sgap_antisymm`, `Sgap_cocycle`) — `S` is relative,
never intrinsic.

* The **upper** direction (`S t ≤ A + B·log t`) is classical-strength argument variation.  Since
  `S = S_class − (strip census − line census)` and that difference is `≥ 0`, it follows from
  Backlund alone (which is *not* compiled in this tree; the gluing is height-centered Jensen +
  argument bookkeeping, the remaining classical-tier work).
* The **lower** direction (`−S t ≤ A + B·log t`) unpacks, given Backlund, to a bound on the
  count of chart zeros with no on-line source at log resolution.  Stated precisely: what the
  difference `S_class − S` counts is `N_strip − N_line`, and because `zeroEventCount` is an
  `ncard` of *ordinates* it is multiplicity-free — so the quantity bounded is the off-line
  census **with multiplicity, plus the on-line multiplicity excess**, not off-line zeros alone.
  Both summands vanish exactly under RH-with-simple-zeros.

That second direction is **not** an analytic estimate of the same species as the first.  It is
the registration/seat question — which chart zeros have native sources — at a weaker quantifier
than RH.  It belongs with the saturation cluster, not with Jensen/Backlund:
`GramRegistrationCapstone.grh_iff_spectral_gram_registration`,
`HarmonicPencilCell.EveryZeroHasSource` / `everyZeroHasSource_iff_critical`,
`SourceHolonomy.Exhaustive`.  Same species as those, weaker quantifier — not an estimate
awaiting a sharper technique.

**What is chart-dependent here is the filing, not the content.**  The lower direction is a real,
undischarged mathematical statement.  It is *not* vacuous, and the carrier does not dissolve it:
asserting `N_off = 0` natively is exactly RH, and nothing here gets that for free.

**Negative result, recorded so it is not re-attempted.**  Density/proportion results cannot
reach the lower direction.  Zeta23's Theorem A (`Zeta23.thmA_cumulative`, `(2/3 − ε)·N ≤ N₀*`)
bounds the sourceless count by `(1/3 + ε)·N(T)`, and `N(T)` is of order `T·log T`
(`CountingDataZeta.zetaCountingData`, `cmain = 1/(2π)`).  The lower direction needs order
`log T`.  That is a factor of `T` — a different regime, not a constant to be improved.  Any
future attempt routed through a density or positive-proportion input hits this wall first.

## `log t` is a count, not an estimate: the native reading

`log t` in these targets is not an estimate-shaped quantity — it is the local zero density.
Riemann–von Mangoldt gives `dN/dt = (1/2π)·log(t/2π)`, so, with the normalization written out
and *not* rounded to a proportionality,

  `log t = 2π · (dN/dt) + log 2π`,

i.e. `log t` is `2π` times the number of zeros per unit ordinate at height `t`, up to the
additive `log 2π ≈ 1.838`.  (The same constant is the `κ = log 2π + 1` of
`CountingDataZeta.profileDiff_sub_main`.)  This also identifies the clock rate: `clockRate`
is `π` times that local density, since `ClockRateStirling.clockRate_eq_pi_mul_mu` gives
`clockRate t = π · Zeta23.mu t` and `mu` is the archimedean density.  So writing these targets
as `O(log t)` disguises a counting statement as an analytic one — the same register error
diagnosed above for the lower direction.

**Change of variables `t = eᵘ`, stated completely.**  The defect-shaped quantities linearize:

  `|S| ≤ A + B·log t` ⟼ `|S(eᵘ)| ≤ A + B·u`  (`carrierJensenBound_native`),
  `N_sourceless ≤ C·log t` ⟼ `≤ C·u`,   `clockRate ≤ A' + (1/2)·log t` ⟼ `≤ A' + u/2`.

But the main terms get *worse*, and that must be reported alongside: the census
`N(t) = (t/2π)(log(t/2π) − 1)` becomes `(eᵘ/2π)(u − log 2π − 1)`, the clock `ϑ(t)` likewise
acquires an `eᵘ` factor, and the density `dN/du = (1/2π)(u − log 2π)·eᵘ` is exponential in `u`.
So this is a trade — errors linear, main terms exponential — **not** a simplification, and
above all **not** a proof: `C·u` and `C·log t` are the same inequality, and a wall is not moved
by substitution.

**Which logarithm this is.**  Two distinct logarithms are in play and must not be conflated.
(a) The geometric-to-analytic height relation `reprPoint χ Z = 1/2 + i·log Z`
(`HarmonicPencilCell.reprPoint`, `FocalCancellationFindsZeros.reprPoint_exp`), with
`exp_height_ne_analytic_height` recording that the two heights genuinely differ; this is the
carrier's own log-coordinate, the one in which strand heights are `log p`, dilation is
translation, and the reflection is `u ↦ −u`.  (b) The density logarithm above, which comes from
the Γ-factor/conductor.  The substitution `u = log t` is **(b), not (a)** — and since (a) already
sets `t = log Z`, it is a *second* logarithm, `u = log log Z`.  It is therefore a different
coordinate from the carrier's log-register, not the same one reached by another route.  Saying
so plainly is more useful than forcing the identification: no strand-height, reflection, or
dilation structure transports to `u` for free.

**Consequence for method selection.**  In the chart these read as analytic estimates and invite
Jensen / Backlund / argument-variation tools — which, per the negative result above, cannot
reach the lower direction.  In native units they read as counting statements about the carrier:
"sourceless zeros accumulate at most linearly in native height", "at most one event per closed
cell".  That is the register in which `carrier_attribution`, `SourceHolonomy`, and the
registration capstone live, and it is where the next attack on the lower direction should start.

## Compiled anchors

`xi_zero_count_disk_bound` with `xi_bound_in_strip` (`ZeroCountJensen.lean`) supply the Jensen
census machinery — origin-centered `N(R) ≤ C·R·log R` compiled outright; the per-window form
re-runs the same circle-average argument on height-centered disks using the strip bound.  The
clock-rate hypothesis `hclock` of `carrierJensenBound_of_clockBound` is **discharged**
unconditionally in `ClockRateStirling.lean` (`clockRate_log_bound_half`, coefficient exactly
`1/2`); the Γ-modulus ladder of `StirlingBound.lean` is no longer the route to it.
-/

namespace CriticalLinePhasor.CarrierScale

/-- **The defect increment identity.**  Over any window the change of the compensation ledger is
exactly the census increment minus the clock advance in units of `π`. -/
theorem S_increment (t t' : ℝ) :
    S t - S t' =
      ((zeroEventCount t : ℝ) - (zeroEventCount t' : ℝ)) - (theta t - theta t') / Real.pi := by
  unfold S
  ring

/-- The trivial two-ledger bound: the defect never exceeds the census plus the clock. -/
theorem S_ledger_bound (t : ℝ) :
    |S t| ≤ (zeroEventCount t : ℝ) + 1 + |theta t| / Real.pi := by
  unfold S
  have hπ : 0 < Real.pi := Real.pi_pos
  calc |(zeroEventCount t : ℝ) - 1 - theta t / Real.pi|
      ≤ |(zeroEventCount t : ℝ) - 1| + |theta t / Real.pi| := abs_sub _ _
    _ ≤ ((zeroEventCount t : ℝ) + 1) + |theta t| / Real.pi := by
        gcongr
        · calc |(zeroEventCount t : ℝ) - 1| ≤ |(zeroEventCount t : ℝ)| + |(1 : ℝ)| := abs_sub _ _
            _ = (zeroEventCount t : ℝ) + 1 := by
                rw [abs_one, abs_of_nonneg (by positivity : (0:ℝ) ≤ (zeroEventCount t : ℝ))]
        · rw [abs_div, abs_of_pos hπ]

/-- **The carrier Jensen target, native register.**  The defect is bounded by a constant number
of local window budgets: the clock rate is the growth budget per window. -/
def CarrierJensenClockBound (A B : ℝ) : Prop :=
  ∀ t : ℝ, 2 ≤ t → |S t| ≤ A + B * clockRate t

/-- **The carrier Jensen target, chart register.**  Backlund's bound, `S(t) = O(log t)`, as the
chart reading of the native form. -/
def CarrierJensenBound (A B : ℝ) : Prop :=
  ∀ t : ℝ, 2 ≤ t → |S t| ≤ A + B * Real.log t

/-- The native register implies the chart register once the clock rate is bounded by the chart's
logarithm (the Stirling brick, named as the hypothesis `hclock`). -/
theorem carrierJensenBound_of_clockBound (A B A' B' : ℝ) (hB : 0 ≤ B)
    (hclock : ∀ t : ℝ, 2 ≤ t → clockRate t ≤ A' + B' * Real.log t)
    (h : CarrierJensenClockBound A B) :
    CarrierJensenBound (A + B * A') (B * B') := by
  intro t ht
  calc |S t| ≤ A + B * clockRate t := h t ht
    _ ≤ A + B * (A' + B' * Real.log t) := by
        have := hclock t ht
        nlinarith
    _ = A + B * A' + B * B' * Real.log t := by ring

/-- **The chart target in native height.**  Under `t = eᵘ` the chart bound reads linearly in
native height: the accumulated defect grows at most linearly in `u`.

This proves nothing and is not intended to.  `A + B·u` and `A + B·log t` are the same
inequality, and a wall is not moved by a change of variables.  It is recorded because the two
readings *select different toolkits* — see the register note at the head of this file — and
because the native form is the one in which the residual direction is a counting statement
about the carrier rather than an analytic estimate. -/
theorem carrierJensenBound_native {A B : ℝ} (h : CarrierJensenBound A B) :
    ∀ u : ℝ, Real.log 2 ≤ u → |S (Real.exp u)| ≤ A + B * u := by
  intro u hu
  have h2 : (2 : ℝ) ≤ Real.exp u := by
    have hm := Real.exp_le_exp.mpr hu
    rwa [Real.exp_log (by norm_num : (0 : ℝ) < 2)] at hm
  simpa [Real.log_exp] using h (Real.exp u) h2

/-- Every on-line event through height `t` is a ξ-zero in the origin ball of radius `t + 1`. -/
theorem event_line_mem_xiZeros_ball {t : ℝ} (ht : 0 ≤ t) {γ : ℝ}
    (hγ : γ ∈ Set.Ioc 0 t ∧ riemannZeta (line γ) = 0) :
    line γ ∈ Metric.closedBall (0 : ℂ) (t + 1) ∩ {z | ZD.riemannXi z = 0} := by
  constructor
  · rw [Metric.mem_closedBall, dist_zero_right, line_def]
    have h1 : |γ| ≤ t := abs_le.mpr ⟨by linarith [hγ.1.1], hγ.1.2⟩
    calc ‖(1 / 2 : ℂ) + (γ : ℂ) * Complex.I‖
        ≤ ‖(1 / 2 : ℂ)‖ + ‖(γ : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = 1 / 2 + |γ| := by simp
      _ ≤ t + 1 := by linarith
  · show ZD.riemannXi (line γ) = 0
    apply ZD.ZeroCount.riemannXi_zero_of_mem_NontrivialZeros
    exact ⟨by rw [line_re]; norm_num, by rw [line_re]; norm_num, hγ.2⟩

/-- **The census disk wire.**  The on-line census through height `t` injects into the ξ-zeros of
the origin ball of radius `t + 1`. -/
theorem zeroEventCount_le_xiZeros_ball (t : ℝ) (ht : 0 ≤ t) :
    zeroEventCount t ≤
      (Metric.closedBall (0 : ℂ) (t + 1) ∩ {z | ZD.riemannXi z = 0}).ncard := by
  unfold zeroEventCount
  refine Set.ncard_le_ncard_of_injOn (fun γ => line γ) ?_ ?_
    (ZD.ZeroCount.riemannXi_zeros_finite_in_closedBall (t + 1))
  · intro γ hγ
    exact event_line_mem_xiZeros_ball ht hγ
  · intro γ₁ _ γ₂ _ h
    have him := congrArg Complex.im h
    simpa [line_def] using him

/-- **Unconditional census growth.**  The line census is `O(t·log t)`: the compiled Jensen disk
count caps the number of on-line events — the first growth bound on the census in the tree,
consumed from `ZD.ZeroCount.xi_zero_count_disk_bound` with no new analysis. -/
theorem census_polynomial_bound :
    ∃ C > (0 : ℝ), ∃ t₀ > (0 : ℝ), ∀ t : ℝ, t₀ ≤ t →
      (zeroEventCount t : ℝ) ≤ C * (t + 1) * Real.log (t + 1) := by
  obtain ⟨C, hC, R₀, hR₀, hB⟩ := ZD.ZeroCount.xi_zero_count_disk_bound
  refine ⟨C, hC, max R₀ 1, lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
  intro t htt
  have ht0 : (0 : ℝ) ≤ t := le_trans (by norm_num) (le_trans (le_max_right R₀ 1) htt)
  have hR : R₀ ≤ t + 1 := by
    have := le_trans (le_max_left R₀ 1) htt
    linarith
  calc (zeroEventCount t : ℝ)
      ≤ ((Metric.closedBall (0 : ℂ) (t + 1) ∩ {z | ZD.riemannXi z = 0}).ncard : ℝ) := by
        exact_mod_cast zeroEventCount_le_xiZeros_ball t ht0
    _ ≤ C * (t + 1) * Real.log (t + 1) := hB (t + 1) hR

end CriticalLinePhasor.CarrierScale

#print axioms CriticalLinePhasor.CarrierScale.S_increment
#print axioms CriticalLinePhasor.CarrierScale.S_ledger_bound
#print axioms CriticalLinePhasor.CarrierScale.carrierJensenBound_of_clockBound
#print axioms CriticalLinePhasor.CarrierScale.carrierJensenBound_native
#print axioms CriticalLinePhasor.CarrierScale.zeroEventCount_le_xiZeros_ball
#print axioms CriticalLinePhasor.CarrierScale.census_polynomial_bound
