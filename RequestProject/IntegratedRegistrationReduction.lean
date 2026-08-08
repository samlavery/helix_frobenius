import RequestProject.ZetaContourArgument

/-!
# The integrated-registration reduction: sublinear mean defect closes the coordinate identity

The `t`-level form of the S(t) identification.  The coordinate defect
`D T = classicalSContour − Smult = offLineStripZeroCountMult T` (the compiled
registration law) is a non-negative, monotone, integer-valued step function of the
height, vanishing below `T = 2`.  A single jump anywhere therefore forces its running
integral to grow linearly.  Consequently the full global coordinate identification —
`classicalSContour hT = Smult T` at every good height — is **equivalent** to mere
sublinearity of the integrated defect:

  `(fun T => ∫ t in 0..T, D t) =o[atTop] (fun T => T)`.

Zeros never enter as a premise: the identity is a statement about two continuous
carrier coordinates in the height variable, and every per-zero statement downstream is
a corollary of this criterion.

* `stripZeroFinset_subset` / `offLineStripZeroCountMult_mono` — the defect is monotone
  in the height (window monotonicity, term-nonnegative sums).
* `eq_zero_of_monotone_nonneg_integral_sublinear` — the real-analysis core: a
  monotone, non-negative function on `ℝ` whose running integral from `0` is `o(T)`
  vanishes on `[0, ∞)`.
* `offLineStripZeroCountMult_eq_zero_of_integral_sublinear` — the defect vanishes at
  **every** height (negative heights by monotonicity from the empty window).
* `globalCoordinateIdentification_of_integral_sublinear` — sublinear integrated defect
  ⟹ `classicalSContour hT = Smult T` at every good height.
* `globalCoordinateIdentification_iff_integral_sublinear` — **the criterion is exact**:
  the global coordinate identification is equivalent to sublinearity of the
  integrated defect.  The S(t) identification is officially a `t`-level statement.

Proven in this file: everything above, unconditionally.  The sublinear bound's
classical-side companion is Littlewood's unconditional `∫₀ᵀ S = O(log T)`.
-/

open Complex Set MeasureTheory Filter Asymptotics
open intervalIntegral

namespace CriticalLinePhasor.ContourArgument

open CriticalLinePhasor CriticalLinePhasor.ResidueJump

/-! ## Monotonicity of the defect -/

/-- The upper-strip zero window grows with the height. -/
theorem stripZeroFinset_subset {T T' : ℝ} (h : T ≤ T') :
    stripZeroFinset T ⊆ stripZeroFinset T' := by
  intro ρ hρ
  have hs := (stripZeroWindow_finite T).mem_toFinset.mp hρ
  exact (stripZeroWindow_finite T').mem_toFinset.mpr ⟨hs.1, hs.2.1, hs.2.2.trans h⟩

/-- The off-line coverage defect is monotone in the height. -/
theorem offLineStripZeroCountMult_mono {T T' : ℝ} (h : T ≤ T') :
    offLineStripZeroCountMult T ≤ offLineStripZeroCountMult T' := by
  classical
  unfold offLineStripZeroCountMult
  exact Finset.sum_le_sum_of_subset
    (Finset.filter_subset_filter _ (stripZeroFinset_subset h))

/-- The defect vanishes at non-positive heights: the upper window is empty. -/
theorem offLineStripZeroCountMult_eq_zero_of_nonpos {T : ℝ} (hT : T ≤ 0) :
    offLineStripZeroCountMult T = 0 := by
  classical
  unfold offLineStripZeroCountMult
  apply Finset.sum_eq_zero
  intro ρ hρ
  have hs := (stripZeroWindow_finite T).mem_toFinset.mp
    (Finset.mem_filter.mp hρ).1
  exact absurd (hs.2.1.trans_le (hs.2.2.trans hT)) (lt_irrefl 0)

/-! ## The real-analysis core -/

/-- **A monotone, non-negative function whose running integral is sublinear vanishes on
the non-negative axis.**  One positive value `c` at `t₀` forces
`∫₀ᵀ f ≥ c·(T − t₀)` for all `T ≥ t₀` — linear growth — contradicting `o(T)`. -/
theorem eq_zero_of_monotone_nonneg_integral_sublinear
    {f : ℝ → ℝ} (hmono : Monotone f) (hnn : ∀ t, 0 ≤ f t)
    (hsub : (fun T => ∫ t in (0:ℝ)..T, f t) =o[atTop] (fun T : ℝ => T))
    {t₀ : ℝ} (ht₀ : 0 ≤ t₀) : f t₀ = 0 := by
  by_contra hne
  have hc : 0 < f t₀ := lt_of_le_of_ne (hnn t₀) (Ne.symm hne)
  set c : ℝ := f t₀ with hcdef
  -- Sublinearity at tolerance `c/2`.
  have hev := (isLittleO_iff.mp hsub) (show (0:ℝ) < c / 2 by positivity)
  rw [eventually_atTop] at hev
  obtain ⟨N, hN⟩ := hev
  -- A height beyond every threshold.
  set T : ℝ := max N (2 * t₀ + 1) with hTdef
  have hTN : N ≤ T := le_max_left _ _
  have hTt₀ : t₀ ≤ T := by
    have : 2 * t₀ + 1 ≤ T := le_max_right _ _
    linarith
  have hT0 : (0:ℝ) ≤ T := le_trans ht₀ hTt₀
  -- Linear lower bound for the running integral.
  have hint₁ : IntervalIntegrable f volume 0 t₀ := hmono.intervalIntegrable
  have hint₂ : IntervalIntegrable f volume t₀ T := hmono.intervalIntegrable
  have hsplit : (∫ t in (0:ℝ)..t₀, f t) + ∫ t in t₀..T, f t
      = ∫ t in (0:ℝ)..T, f t :=
    integral_add_adjacent_intervals hint₁ hint₂
  have hhead : 0 ≤ ∫ t in (0:ℝ)..t₀, f t :=
    integral_nonneg ht₀ (fun t _ => hnn t)
  have htail : (T - t₀) * c ≤ ∫ t in t₀..T, f t := by
    have hconst : ∫ _t in t₀..T, c = (T - t₀) * c := by
      rw [intervalIntegral.integral_const, smul_eq_mul]
    rw [← hconst]
    exact integral_mono_on hTt₀ intervalIntegrable_const hint₂
      (fun t ht => hmono ht.1)
  have hlower : (T - t₀) * c ≤ ∫ t in (0:ℝ)..T, f t := by
    rw [← hsplit]
    linarith
  -- Sublinear upper bound at the same height.
  have hupper : ∫ t in (0:ℝ)..T, f t ≤ c / 2 * T := by
    have h := hN T hTN
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hT0] at h
    exact (le_abs_self _).trans h
  -- `c·(T − t₀) ≤ (c/2)·T` forces `T ≤ 2 t₀`, contradicting `2 t₀ + 1 ≤ T`.
  have hT2t₀ : 2 * t₀ + 1 ≤ T := le_max_right _ _
  nlinarith [hlower.trans hupper]

/-! ## The reduction -/

/-- **Sublinear integrated defect kills the defect at every height.** -/
theorem offLineStripZeroCountMult_eq_zero_of_integral_sublinear
    (hsub : (fun T => ∫ t in (0:ℝ)..T, (offLineStripZeroCountMult t : ℝ))
      =o[atTop] (fun T : ℝ => T)) (T : ℝ) :
    offLineStripZeroCountMult T = 0 := by
  by_cases hT : T ≤ 0
  · exact offLineStripZeroCountMult_eq_zero_of_nonpos hT
  · push_neg at hT
    have hmono : Monotone (fun t : ℝ => (offLineStripZeroCountMult t : ℝ)) :=
      fun a b hab => Nat.cast_le.mpr (offLineStripZeroCountMult_mono hab)
    have h := eq_zero_of_monotone_nonneg_integral_sublinear hmono
      (fun t => Nat.cast_nonneg _) hsub hT.le
    exact_mod_cast h

/-- **The `t`-level closure of the coordinate identity**: sublinearity of the integrated
registration defect yields `classicalSContour = Smult` at every good height. -/
theorem globalCoordinateIdentification_of_integral_sublinear
    (hsub : (fun T => ∫ t in (0:ℝ)..T, (offLineStripZeroCountMult t : ℝ))
      =o[atTop] (fun T : ℝ => T)) :
    ∀ (T : ℝ) (hT : GoodHeight T), classicalSContour hT = Smult T := by
  intro T hT
  rw [classicalSContour_eq_Smult_add_offLine hT,
    offLineStripZeroCountMult_eq_zero_of_integral_sublinear hsub T]
  simp

/-- **The criterion is exact**: the global coordinate identification holds iff the
integrated registration defect is sublinear.  Forward: at any height, a good height
above it bounds the defect by a vanishing one (monotonicity), so the integrand is
identically zero.  The S(t) identification is officially a statement about the
`t`-average of two carrier coordinates; every per-zero statement is downstream. -/
theorem globalCoordinateIdentification_iff_integral_sublinear :
    (∀ (T : ℝ) (hT : GoodHeight T), classicalSContour hT = Smult T) ↔
      (fun T => ∫ t in (0:ℝ)..T, (offLineStripZeroCountMult t : ℝ))
        =o[atTop] (fun T : ℝ => T) := by
  constructor
  · intro hid
    have hzero : ∀ t : ℝ, offLineStripZeroCountMult t = 0 := by
      intro t
      obtain ⟨T', hT't, hT'⟩ := exists_goodHeight_gt t
      have h0 : offLineStripZeroCountMult T' = 0 :=
        (classicalSContour_eq_Smult_iff_offLine_eq_zero hT').mp (hid T' hT')
      exact Nat.le_zero.mp (h0 ▸ offLineStripZeroCountMult_mono hT't.le)
    have hfun : (fun T => ∫ t in (0:ℝ)..T, (offLineStripZeroCountMult t : ℝ))
        = fun _ => (0:ℝ) := by
      funext T
      rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ))
        (fun t _ => by rw [hzero t, Nat.cast_zero])]
      simp
    rw [hfun]
    exact isLittleO_zero _ _
  · exact fun hsub => globalCoordinateIdentification_of_integral_sublinear hsub

end CriticalLinePhasor.ContourArgument

#print axioms CriticalLinePhasor.ContourArgument.stripZeroFinset_subset
#print axioms CriticalLinePhasor.ContourArgument.offLineStripZeroCountMult_mono
#print axioms CriticalLinePhasor.ContourArgument.eq_zero_of_monotone_nonneg_integral_sublinear
#print axioms CriticalLinePhasor.ContourArgument.offLineStripZeroCountMult_eq_zero_of_integral_sublinear
#print axioms CriticalLinePhasor.ContourArgument.globalCoordinateIdentification_of_integral_sublinear
#print axioms CriticalLinePhasor.ContourArgument.globalCoordinateIdentification_iff_integral_sublinear
