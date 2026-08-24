import RequestProject.DVPGramRegistration

/-!
# The Littlewood interface: registration residuals in `N_all`-form

The ledger-391 decomposition, compiled.  With `S_all = S_mult + N_off`:

* `LittlewoodBound` — `|∫₀ᵀ S_all| ≤ C(1 + log(1+T))`, the CLASSICAL
  statement (Littlewood 1924, for the full strip count);
* `OffLineMassLog` — the integrated off-line multiplicity grows at most
  logarithmically (true; RH would make it zero).

These two discharge BOTH non-mass inputs of `gram_registration_reduction`:
the boundary accumulation splits as classical-plus-off-line, and the o(T)
input is the Littlewood bound composed with `log ≪ id`.  Net compiled
statement: on the concrete π-cells, `ClockCellMassBounded` ALONE delivers
the global identification `classicalSContour = Smult` under the two
log-integral controls.
-/

open Complex Filter Topology
open CriticalLinePhasor.CarrierScale CriticalLinePhasor.ContourArgument
open CriticalLinePhasor.ResidueJump

noncomputable section

namespace CriticalLinePhasor.DVP

/-- **The full-strip ledger** `S_all(t) = S_mult(t) + N_off(t)`: the on-line
multiplicity ledger plus the off-line strip census.  This is the object of
Littlewood's classical theorem. -/
noncomputable def SAll (t : ℝ) : ℝ :=
  Smult t + (offLineStripZeroCountMult t : ℝ)

/-- **Littlewood's bound, `N_all`-form**: the running integral of the
full-strip ledger accumulates at most logarithmically. -/
def LittlewoodBound : Prop :=
  ∃ C : ℝ, ∀ T : ℝ, 0 ≤ T →
    |∫ t in (0:ℝ)..T, SAll t| ≤ C * (1 + Real.log (1 + T))

/-- **Off-line-mass log control**: the integrated off-line multiplicity
census grows at most logarithmically.  (Under RH the integrand is zero.) -/
def OffLineMassLog : Prop :=
  ∃ C : ℝ, ∀ T : ℝ, 0 ≤ T →
    (∫ t in (0:ℝ)..T, (offLineStripZeroCountMult t : ℝ))
      ≤ C * (1 + Real.log (1 + T))

/-- The on-line multiplicity count is monotone in the height. -/
theorem zeroEventCountMult_mono :
    Monotone fun t => zeroEventCountMult t := by
  intro a b hab
  unfold zeroEventCountMult
  apply Finset.sum_le_sum_of_subset
  rw [Set.Finite.toFinset_subset_toFinset]
  intro γ' hγ'
  simp only [Set.mem_ofPred_eq, Set.mem_Ioc] at hγ' ⊢
  exact ⟨⟨hγ'.1.1, le_trans hγ'.1.2 hab⟩, hγ'.2⟩

/-- The off-line strip census is monotone in the height. -/
theorem offLineStripZeroCountMult_mono :
    Monotone fun T => offLineStripZeroCountMult T := by
  intro a b hab
  unfold offLineStripZeroCountMult stripZeroFinset
  apply Finset.sum_le_sum_of_subset
  apply Finset.filter_subset_filter
  rw [Set.Finite.toFinset_subset_toFinset]
  intro ρ hρ
  simp only [stripZeroWindow, Set.mem_ofPred_eq] at hρ ⊢
  exact ⟨hρ.1, hρ.2.1, le_trans hρ.2.2 hab⟩

/-- `S_mult` is interval-integrable: monotone count minus continuous clock. -/
theorem smult_intervalIntegrable (a b : ℝ) :
    IntervalIntegrable Smult MeasureTheory.volume a b := by
  have hcount : IntervalIntegrable (fun t => (zeroEventCountMult t : ℝ))
      MeasureTheory.volume a b := by
    apply Monotone.intervalIntegrable
    intro x y hxy
    exact Nat.cast_le.mpr (zeroEventCountMult_mono hxy)
  have htheta : IntervalIntegrable (fun t => 1 + theta t / Real.pi)
      MeasureTheory.volume a b :=
    (continuous_const.add (continuous_theta.div_const _)).intervalIntegrable a b
  have heq : Smult = fun t =>
      (zeroEventCountMult t : ℝ) - (1 + theta t / Real.pi) := by
    funext t
    unfold Smult
    ring
  rw [heq]
  exact hcount.sub htheta

/-- The off-line census is interval-integrable (monotone). -/
theorem offline_intervalIntegrable (a b : ℝ) :
    IntervalIntegrable (fun t => (offLineStripZeroCountMult t : ℝ))
      MeasureTheory.volume a b := by
  apply Monotone.intervalIntegrable
  intro x y hxy
  exact Nat.cast_le.mpr (offLineStripZeroCountMult_mono hxy)

/-- The running `S_mult` integral splits off the full-strip ledger exactly. -/
theorem integral_smult_split (T : ℝ) :
    ∫ t in (0:ℝ)..T, Smult t
      = (∫ t in (0:ℝ)..T, SAll t)
        - ∫ t in (0:ℝ)..T, (offLineStripZeroCountMult t : ℝ) := by
  have hadd : ∫ t in (0:ℝ)..T, SAll t
      = (∫ t in (0:ℝ)..T, Smult t)
        + ∫ t in (0:ℝ)..T, (offLineStripZeroCountMult t : ℝ) := by
    unfold SAll
    exact intervalIntegral.integral_add (smult_intervalIntegrable 0 T)
      (offline_intervalIntegrable 0 T)
  linarith

/-- **The 391 decomposition, compiled**: Littlewood in `N_all`-form plus the
off-line-mass log control deliver the boundary-accumulation residual on any
nonnegative cell decomposition. -/
theorem boundaryLogAccumulation_of_littlewood
    (hLW : LittlewoodBound) (hOff : OffLineMassLog)
    {c : ℕ → ℝ} (hc : ∀ n, 0 ≤ c n) :
    BoundaryLogAccumulation c := by
  obtain ⟨C₁, hC₁⟩ := hLW
  obtain ⟨C₂, hC₂⟩ := hOff
  refine ⟨C₁ + C₂, fun n => ?_⟩
  have hT0 : 0 ≤ c n := hc n
  have hX : (0:ℝ) ≤ 1 + Real.log (1 + c n) := by
    have : (0:ℝ) ≤ Real.log (1 + c n) := Real.log_nonneg (by linarith)
    linarith
  have hoff_nonneg : 0 ≤ ∫ t in (0:ℝ)..(c n),
      (offLineStripZeroCountMult t : ℝ) :=
    intervalIntegral.integral_nonneg hT0 fun t _ => by positivity
  have h1 := hC₁ (c n) hT0
  have h2 := hC₂ (c n) hT0
  have habs : |(∫ t in (0:ℝ)..(c n), SAll t)
        - ∫ t in (0:ℝ)..(c n), (offLineStripZeroCountMult t : ℝ)|
      ≤ |∫ t in (0:ℝ)..(c n), SAll t|
        + ∫ t in (0:ℝ)..(c n), (offLineStripZeroCountMult t : ℝ) := by
    rw [sub_eq_add_neg]
    refine (abs_add_le _ _).trans ?_
    rw [abs_neg, abs_of_nonneg hoff_nonneg]
  have hring : (C₁ + C₂) * (1 + Real.log (1 + c n))
      = C₁ * (1 + Real.log (1 + c n)) + C₂ * (1 + Real.log (1 + c n)) := by
    ring
  rw [integral_smult_split (c n)]
  linarith

/-- **The o(T) input, discharged**: the Littlewood bound alone makes the
running full-strip integral sublinear. -/
theorem littlewood_o_input (hLW : LittlewoodBound) :
    (fun T => ∫ t in (0:ℝ)..T,
        (Smult t + (offLineStripZeroCountMult t : ℝ)))
      =o[atTop] fun T : ℝ => T := by
  obtain ⟨C, hC⟩ := hLW
  have hlog : (fun T : ℝ => Real.log (1 + T)) =o[atTop] fun T : ℝ => T := by
    have h1 : (fun T : ℝ => Real.log (1 + T))
        =o[atTop] fun T : ℝ => 1 + T := by
      have := Real.isLittleO_log_id_atTop.comp_tendsto
        (tendsto_atTop_add_const_left atTop 1 tendsto_id)
      simpa [Function.comp_def] using this
    have h2 : (fun T : ℝ => 1 + T) =O[atTop] fun T : ℝ => T := by
      rw [Asymptotics.isBigO_iff]
      refine ⟨2, ?_⟩
      filter_upwards [eventually_ge_atTop (1:ℝ)] with T hT
      rw [Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 + T),
        abs_of_nonneg (by linarith : (0:ℝ) ≤ T)]
      linarith
    exact h1.trans_isBigO h2
  have hone : (fun _ : ℝ => (1:ℝ)) =o[atTop] fun T : ℝ => T := by
    rw [Asymptotics.isLittleO_const_left]
    right
    simpa only [Function.comp_def, Real.norm_eq_abs]
      using tendsto_abs_atTop_atTop
  have hmaj : (fun T : ℝ => 1 + Real.log (1 + T)) =o[atTop] fun T : ℝ => T :=
    hone.add hlog
  have hO : (fun T => ∫ t in (0:ℝ)..T,
      (Smult t + (offLineStripZeroCountMult t : ℝ)))
      =O[atTop] fun T : ℝ => 1 + Real.log (1 + T) := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨C, ?_⟩
    filter_upwards [eventually_ge_atTop (0:ℝ)] with T hT0
    have h := hC T hT0
    unfold SAll at h
    have hX : (0:ℝ) ≤ 1 + Real.log (1 + T) := by
      have : (0:ℝ) ≤ Real.log (1 + T) := Real.log_nonneg (by linarith)
      linarith
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hX]
    exact h
  exact hO.trans_isLittleO hmaj

/-- **The identification reduced to ONE register residual**: under Littlewood
(`N_all`-form) and the off-line-mass log control, there are concrete π-cells
on which `ClockCellMassBounded` alone delivers `classicalSContour = Smult`
at every good height. -/
theorem gram_registration_from_littlewood
    (hLW : LittlewoodBound) (hOff : OffLineMassLog) :
    ∃ c : ℕ → ℝ, c 0 = 10 ∧ Monotone c
      ∧ (∀ n, theta (c (n + 1)) - theta (c n) = Real.pi)
      ∧ (ClockCellMassBounded c →
          ∀ (T : ℝ) (hT : GoodHeight T), classicalSContour hT = Smult T) := by
  obtain ⟨c, hc0, hmono, hspan, himp⟩ := gram_registration_reduction
  refine ⟨c, hc0, hmono, hspan, fun hmass => ?_⟩
  have hc_nonneg : ∀ n, 0 ≤ c n := by
    intro n
    have h10 : (10:ℝ) ≤ c n := by
      rw [← hc0]
      exact hmono (Nat.zero_le n)
    linarith
  exact himp hmass
    (boundaryLogAccumulation_of_littlewood hLW hOff hc_nonneg)
    (littlewood_o_input hLW)

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.zeroEventCountMult_mono
#print axioms CriticalLinePhasor.DVP.offLineStripZeroCountMult_mono
#print axioms CriticalLinePhasor.DVP.smult_intervalIntegrable
#print axioms CriticalLinePhasor.DVP.integral_smult_split
#print axioms CriticalLinePhasor.DVP.boundaryLogAccumulation_of_littlewood
#print axioms CriticalLinePhasor.DVP.littlewood_o_input
#print axioms CriticalLinePhasor.DVP.gram_registration_from_littlewood
end AxiomAudit
