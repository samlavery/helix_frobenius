import RequestProject.ResidueJump

/-!
# The exact clock--jump law for the multiplicity ledger

This file packages the non-asymptotic rule carried by the line ledger.  Its two inputs are
defined independently:

* `intervalMultiplicity a b` is the sum of the analytic vanishing orders of
  `ζ(1/2 + iγ)` over `a < γ ≤ b`;
* `theta b - theta a` is the integrated Archimedean clock advance.

For `0 ≤ a ≤ b`, the change of `Smult` is exactly the first quantity minus the second in
units of `π`.  Thus the ledger has a completely determined continuous motion between events
and a completely determined jump at every event.
-/

open Complex Filter Set Topology

namespace CriticalLinePhasor.ResidueJump

open CriticalLinePhasor CriticalLinePhasor.CarrierScale

/-- The multiplicity of the critical-line events in `(a, b]`. -/
noncomputable def intervalMultiplicity (a b : ℝ) : ℕ :=
  ∑ γ ∈ (eventWindow b).filter (fun γ => a < γ), eventOrder γ

/-- Membership in the interval-event window has the direct analytic meaning
`a < γ ≤ b`, `γ > 0`, and `ζ(1/2+iγ)=0`. -/
theorem mem_intervalEventWindow_iff {a b γ : ℝ} :
    γ ∈ (eventWindow b).filter (fun γ => a < γ) ↔
      a < γ ∧ 0 < γ ∧ γ ≤ b ∧ riemannZeta (line γ) = 0 := by
  simp [eventWindow, Set.Finite.mem_toFinset, and_assoc, and_left_comm, and_comm]

/-- The cumulative multiplicity count splits exactly at every nonnegative intermediate
height. -/
theorem zeroEventCountMult_add_intervalMultiplicity {a b : ℝ} (_ha : 0 ≤ a) (hab : a ≤ b) :
    zeroEventCountMult b = zeroEventCountMult a + intervalMultiplicity a b := by
  classical
  unfold zeroEventCountMult intervalMultiplicity eventWindow
  rw [← Finset.sum_union]
  · congr 1
    ext γ
    simp only [Set.Finite.mem_toFinset, Finset.mem_union, Finset.mem_filter, Set.mem_setOf_eq,
      Set.mem_Ioc]
    constructor
    · rintro ⟨⟨hγ0, hγb⟩, hz⟩
      by_cases hγa : γ ≤ a
      · exact Or.inl ⟨⟨hγ0, hγa⟩, hz⟩
      · exact Or.inr ⟨⟨⟨hγ0, hγb⟩, hz⟩, lt_of_not_ge hγa⟩
    · rintro (⟨⟨hγ0, hγa⟩, hz⟩ | ⟨⟨⟨hγ0, hγb⟩, hz⟩, -⟩)
      · exact ⟨⟨hγ0, hγa.trans hab⟩, hz⟩
      · exact ⟨⟨hγ0, hγb⟩, hz⟩
  · rw [Finset.disjoint_left]
    intro γ hγa hγab
    have hle : γ ≤ a := ((events_finite a).mem_toFinset.mp hγa).1.2
    have hlt : a < γ := (Finset.mem_filter.mp hγab).2
    exact (not_lt_of_ge hle) hlt

/-- The Gamma clock advance is exactly the integral of `clockRate` over the interval. -/
theorem theta_sub_theta (a b : ℝ) :
    theta b - theta a = ∫ t in a..b, clockRate t := by
  unfold theta
  exact intervalIntegral.integral_interval_sub_left
    (continuous_clockRate.intervalIntegrable 0 b)
    (continuous_clockRate.intervalIntegrable 0 a)

/-- **Exact clock--jump law.**  On every interval `0 ≤ a ≤ b`,

`S_mult(b) - S_mult(a) = multiplicity(a,b] - (1/π) ∫_a^b clockRate(t) dt`.

The discrete term is defined from analytic vanishing orders; the continuous term is defined
from the Archimedean Gamma factor. -/
theorem Smult_interval_clock_jump {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    Smult b - Smult a =
      (intervalMultiplicity a b : ℝ) - (∫ t in a..b, clockRate t) / Real.pi := by
  unfold Smult
  rw [zeroEventCountMult_add_intervalMultiplicity ha hab]
  push_cast
  calc
    (zeroEventCountMult a : ℝ) + intervalMultiplicity a b - 1 - theta b / Real.pi -
        ((zeroEventCountMult a : ℝ) - 1 - theta a / Real.pi) =
        (intervalMultiplicity a b : ℝ) - (theta b - theta a) / Real.pi := by ring
    _ = (intervalMultiplicity a b : ℝ) -
        (∫ t in a..b, clockRate t) / Real.pi := by rw [theta_sub_theta]

/-- **Finite-window clock--jump bound.**  The total ledger variation is bounded by the
analytic multiplicity mass in the window plus the absolute Gamma-clock budget. -/
theorem abs_Smult_interval_le_multiplicity_add_clock {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    |Smult b - Smult a| ≤
      (intervalMultiplicity a b : ℝ) + (∫ t in a..b, |clockRate t|) / Real.pi := by
  rw [Smult_interval_clock_jump ha hab]
  calc
    |(intervalMultiplicity a b : ℝ) - (∫ t in a..b, clockRate t) / Real.pi|
        ≤ |(intervalMultiplicity a b : ℝ)| +
            |(∫ t in a..b, clockRate t) / Real.pi| := abs_sub _ _
    _ = (intervalMultiplicity a b : ℝ) +
        |∫ t in a..b, clockRate t| / Real.pi := by
          rw [abs_of_nonneg (Nat.cast_nonneg _), abs_div, abs_of_pos Real.pi_pos]
    _ ≤ (intervalMultiplicity a b : ℝ) +
        (∫ t in a..b, |clockRate t|) / Real.pi := by
          gcongr
          simpa only [Real.norm_eq_abs] using
            (intervalIntegral.norm_integral_le_integral_norm hab (f := clockRate))

/-- A zero-free interval carries no discrete term: the ledger moves only by the Gamma clock. -/
theorem intervalMultiplicity_eq_zero_of_event_free {a b : ℝ}
    (hfree : ∀ γ ∈ Set.Ioc a b, riemannZeta (line γ) ≠ 0) :
    intervalMultiplicity a b = 0 := by
  classical
  unfold intervalMultiplicity
  apply Finset.sum_eq_zero
  intro γ hγ
  have hm := mem_intervalEventWindow_iff.mp hγ
  exact (hfree γ ⟨hm.1, hm.2.2.1⟩ hm.2.2.2).elim

/-- On a zero-free interval the clock--jump law reduces to an exact integral formula. -/
theorem Smult_interval_eq_clock_of_event_free {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hfree : ∀ γ ∈ Set.Ioc a b, riemannZeta (line γ) ≠ 0) :
    Smult b - Smult a = -(∫ t in a..b, clockRate t) / Real.pi := by
  rw [Smult_interval_clock_jump ha hab, intervalMultiplicity_eq_zero_of_event_free hfree]
  ring

/-- **Zero-free interval bound.**  The ledger variation between events is bounded solely by
the total absolute Gamma-clock advance. -/
theorem abs_Smult_interval_le_clock_of_event_free {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hfree : ∀ γ ∈ Set.Ioc a b, riemannZeta (line γ) ≠ 0) :
    |Smult b - Smult a| ≤ (∫ t in a..b, |clockRate t|) / Real.pi := by
  rw [Smult_interval_eq_clock_of_event_free ha hab hfree, abs_div, abs_neg,
    abs_of_pos Real.pi_pos]
  gcongr
  simpa only [Real.norm_eq_abs] using
    (intervalIntegral.norm_integral_le_integral_norm hab (f := clockRate))

/-- On a zero-free open interval, `S_mult` has the forced velocity
`-clockRate/π` at every interior point. -/
theorem Smult_hasDerivWithinAt_of_event_free {a b t : ℝ} (ht : t ∈ Set.Ioo a b)
    (hfree : ∀ γ ∈ Set.Ioc a b, riemannZeta (line γ) ≠ 0) :
    HasDerivWithinAt Smult (-clockRate t / Real.pi) (Set.Ioo a b) t := by
  have hcount : ∀ u ∈ Set.Ioo a b, zeroEventCountMult u = zeroEventCountMult t := by
    intro u hu
    rcases le_total u t with hut | htu
    · exact (multCount_const_of_event_free hut fun γ hγ =>
        hfree γ ⟨hu.1.trans hγ.1, (hγ.2.trans_lt ht.2).le⟩).symm
    · exact multCount_const_of_event_free htu fun γ hγ =>
        hfree γ ⟨ht.1.trans hγ.1, (hγ.2.trans_lt hu.2).le⟩
  let smooth : ℝ → ℝ := fun u =>
    (zeroEventCountMult t : ℝ) - 1 - theta u / Real.pi
  have hsmooth : HasDerivAt smooth (-clockRate t / Real.pi) t := by
    have h := (hasDerivAt_const t ((zeroEventCountMult t : ℝ) - 1)).sub
      ((theta_hasDerivAt t).div_const Real.pi)
    change HasDerivAt (fun u => (zeroEventCountMult t : ℝ) - 1 - theta u / Real.pi)
      (0 - clockRate t / Real.pi) t at h
    simpa only [smooth, zero_sub, neg_div] using h
  apply hsmooth.hasDerivWithinAt.congr
  · intro u hu
    unfold Smult smooth
    rw [hcount u hu]
  · unfold Smult smooth
    rfl

end CriticalLinePhasor.ResidueJump

#print axioms CriticalLinePhasor.ResidueJump.zeroEventCountMult_add_intervalMultiplicity
#print axioms CriticalLinePhasor.ResidueJump.Smult_interval_clock_jump
#print axioms CriticalLinePhasor.ResidueJump.abs_Smult_interval_le_multiplicity_add_clock
#print axioms CriticalLinePhasor.ResidueJump.abs_Smult_interval_le_clock_of_event_free
#print axioms CriticalLinePhasor.ResidueJump.Smult_hasDerivWithinAt_of_event_free
