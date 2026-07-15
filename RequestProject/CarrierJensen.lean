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
* `CarrierJensenClockBound` / `CarrierJensenBound` (named targets) — **register, exactly**: `S`
  here is the LINE ledger, so the two bounds are one-sided-asymmetric in strength.  The *upper*
  side (`S t ≤ A + B·log t`) is classical strength — Backlund's argument-variation bound
  transported, since the line census is dominated by the strip census; its gluing is the
  height-centered Jensen + argument bookkeeping, the remaining classical-tier work.  The *lower*
  side (`−S t ≤ A + B·log t`) is equivalent to `N_off(t) ≤ C·log t` — the off-line census bounded
  at log resolution — which is quantitative zero-set exhaustion, far beyond classical knowledge:
  the two-sided target is where the S(t) program and the exhaustion wall of the GRH part meet.
  Neither target is asserted; the types pin them.

The analytic anchors for both targets are already compiled in-tree (the promoted analytic layer):
`stirling_at_half` and the `norm_Gamma_step` ladder (`StirlingBound.lean`) supply the two-sided
Γ-modulus control from which the clock-rate bound `hclock` glues (a Borel--Carathéodory/Cauchy
derivative step on the ladder), and `xi_zero_count_disk_bound` with `xi_bound_in_strip`
(`ZeroCountJensen.lean`) supply the Jensen census machinery — origin-centered `N(R) ≤ C·R·log R`
compiled outright; the per-window form re-runs the same circle-average argument on height-centered
disks using the strip bound.  The remaining work of this tier is that gluing — assembly of
compiled pieces, not new analysis.  Nothing in this file assumes or proves RH/GRH; both targets
are unconditional classical statements in the 1D chart, restated natively.
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
#print axioms CriticalLinePhasor.CarrierScale.zeroEventCount_le_xiZeros_ball
#print axioms CriticalLinePhasor.CarrierScale.census_polynomial_bound
