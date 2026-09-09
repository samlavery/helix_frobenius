import RequestProject.RadialLogMass
import RequestProject.HelixRegistrationWarp

/-!
Exact cell balances for the existing crossing ledger and radial log-mass.
The partition identities retain the defect and all analytic multiplicities.
The limit transport lemmas explicitly require convergence of the boundary
residues; this file does not establish that convergence or `RadialNoResidue`.
-/

set_option autoImplicit false

open Complex MeasureTheory Set Filter Topology
open scoped BigOperators
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.ResidueJump

namespace CriticalLinePhasor.DVP

/-- The actual crossing integral minus the actual radial boundary change. -/
noncomputable def radialResidue (a b : ℝ) : ℝ :=
  Real.pi * (∫ t in a..b, Smult t) - (radialLogMass b - radialLogMass a)

theorem radialResidue_self (a : ℝ) : radialResidue a a = 0 := by
  simp [radialResidue]

/-- Exact additivity holds even at endpoint zeros and for coincident endpoints. -/
theorem radialResidue_add (a b c : ℝ) :
    radialResidue a b + radialResidue b c = radialResidue a c := by
  have hi := intervalIntegral.integral_add_adjacent_intervals
    (smult_intervalIntegrable a b) (smult_intervalIntegrable b c)
  unfold radialResidue
  rw [← hi]
  ring

/-- All cell boundaries telescope; this does not discard the cell residues. -/
theorem radialResidue_telescope (c : ℕ → ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range n, radialResidue (c k) (c (k + 1)) =
      radialResidue (c 0) (c n) := by
  induction n with
  | zero => simp [radialResidue_self]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    exact radialResidue_add _ _ _

/-- The exact finite-cell decomposition retains the final partial cell. -/
theorem radialResidue_cells_and_remainder (c : ℕ → ℝ) (n : ℕ) (T : ℝ) :
    radialResidue (c 0) T =
      (∑ k ∈ Finset.range n, radialResidue (c k) (c (k + 1))) +
        radialResidue (c n) T := by
  rw [radialResidue_telescope, radialResidue_add]

theorem radialResidue_eq_neg_defect {a b : ℝ}
    (ha : GoodHeight a) (hb : GoodHeight b) (hab : a ≤ b) :
    radialResidue a b = -(Real.pi * ∫ t in a..b, (offLineStripZeroCountMult t : ℝ)) :=
  residue_identity ha hb hab

theorem radialResidue_nonpos {a b : ℝ}
    (ha : GoodHeight a) (hb : GoodHeight b) (hab : a ≤ b) : radialResidue a b ≤ 0 :=
  sub_nonpos.mpr (residue_nonpos ha hb hab)

/-- Extending the window cannot increase its residue. -/
theorem radialResidue_antitone_right {a b c : ℝ}
    (hb : GoodHeight b) (hc : GoodHeight c) (hbc : b ≤ c) :
    radialResidue a c ≤ radialResidue a b := by
  have hneg := radialResidue_nonpos hb hc hbc
  have hadd := radialResidue_add a b c
  linarith

/-- A negative residue in one cell survives every enclosing good window. -/
theorem radialResidue_le_subwindow {a b c d : ℝ}
    (ha : GoodHeight a) (hb : GoodHeight b) (hc : GoodHeight c) (hd : GoodHeight d)
    (hab : a ≤ b) (hcd : c ≤ d) : radialResidue a d ≤ radialResidue b c := by
  have hl := radialResidue_nonpos ha hb hab
  have hr := radialResidue_nonpos hc hd hcd
  have h₁ := radialResidue_add a b c
  have h₂ := radialResidue_add a c d
  linarith

/-- Nonpositive cell residues cannot cancel one another. -/
theorem radialResidue_zero_iff_cells_zero (c : ℕ → ℝ) (n : ℕ)
    (hc : ∀ k ≤ n, GoodHeight (c k))
    (hmono : ∀ k < n, c k ≤ c (k + 1)) :
    radialResidue (c 0) (c n) = 0 ↔
      ∀ k < n, radialResidue (c k) (c (k + 1)) = 0 := by
  rw [← radialResidue_telescope]
  have hneg : ∀ k ∈ Finset.range n, radialResidue (c k) (c (k + 1)) ≤ 0 := by
    intro k hk
    have hkn := Finset.mem_range.mp hk
    exact radialResidue_nonpos (hc k (by omega)) (hc (k + 1) (by omega)) (hmono k hkn)
  simpa using Finset.sum_eq_zero_iff_of_nonpos hneg

/-- A complete off-carrier pair contributes at least its multiplicity times
the window width, even if its registration phases coincide. -/
theorem radialResidue_le_neg_pair {a b : ℝ}
    (ha : GoodHeight a) (hb : GoodHeight b) (hab : a ≤ b)
    (hpair : offLineStripZeroCountMult a ≠ 0) :
    radialResidue a b ≤ -(2 * Real.pi * (b - a)) := by
  have hcount := two_le_offLineStripZeroCountMult hpair
  have hi : (∫ t in a..b, (2 : ℝ)) ≤
      ∫ t in a..b, (offLineStripZeroCountMult t : ℝ) := by
    apply intervalIntegral.integral_mono_on hab intervalIntegrable_const
      (offline_intervalIntegrable a b)
    intro t ht
    exact_mod_cast hcount.trans (offLineStripZeroCountMult_mono ht.1)
  rw [intervalIntegral.integral_const, smul_eq_mul] at hi
  rw [radialResidue_eq_neg_defect ha hb hab]
  nlinarith [Real.pi_pos]

/-- The final partial cell is bounded by the whole enclosing cell. -/
theorem radialResidue_remainder_bounds {a T b : ℝ}
    (ha : GoodHeight a) (hT : GoodHeight T) (hb : GoodHeight b)
    (haT : a ≤ T) (hTb : T ≤ b) :
    radialResidue a b ≤ radialResidue a T ∧ radialResidue a T ≤ 0 :=
  ⟨radialResidue_antitone_right hT hb hTb, radialResidue_nonpos ha hT haT⟩

/-- The full-register balance telescopes with no omitted boundary contribution. -/
theorem radial_boundary_eq_cells (c : ℕ → ℝ) (n : ℕ)
    (hc0 : GoodHeight (c 0)) (hcn : GoodHeight (c n)) (horder : c 0 ≤ c n) :
    radialLogMass (c n) - radialLogMass (c 0) =
      Real.pi * ∑ k ∈ Finset.range n, ∫ t in (c k)..(c (k + 1)), SAll t := by
  rw [intervalIntegral.sum_integral_adjacent_intervals
    (fun k _ => sall_intervalIntegrable (c k) (c (k + 1)))]
  exact (integral_SAll_eq_radialLogMass_sub hc0 hcn horder).symm

/-- The full and on-line registrations have the same circle projection at every height. -/
theorem registrationPhase_SAll_eq_Smult (t : ℝ) :
    registrationPhase (SAll t) = registrationPhase (Smult t) := by
  unfold SAll
  rw [offLineStripZeroCountMult_eq_two_mul_right, Nat.cast_mul, Nat.cast_ofNat]
  exact registrationPhase_add_two_mul_nat _ _

/-- The integrated third coordinate of the registration lift retains precisely
the radial residue. Circle projection is not used to remove this coordinate. -/
theorem radialResidue_eq_integrated_lift_gap {a b : ℝ}
    (ha : GoodHeight a) (hb : GoodHeight b) (hab : a ≤ b) :
    radialResidue a b = -(Real.pi * ∫ t in a..b,
      ((registrationHelix (SAll t)).2 - (registrationHelix (Smult t)).2)) := by
  rw [radialResidue_eq_neg_defect ha hb hab]
  congr 2
  apply intervalIntegral.integral_congr
  intro t _
  simp [registrationHelix, SAll]

/-- If the actual boundary residues tend to zero along unbounded good heights,
every enclosed good window has zero residue. No separate partial-cell bound is needed. -/
theorem radialResidue_zero_of_boundary_limit {a b : ℝ} {c : ℕ → ℝ}
    (ha : GoodHeight a) (hb : GoodHeight b) (hab : a ≤ b)
    (hc : ∀ n, GoodHeight (c n)) (htop : Tendsto c atTop atTop)
    (hlim : Tendsto (fun n => radialResidue a (c n)) atTop (𝓝 0)) :
    radialResidue a b = 0 := by
  apply le_antisymm (radialResidue_nonpos ha hb hab)
  apply le_of_tendsto hlim
  filter_upwards [htop.eventually_ge_atTop b] with n hn
  exact radialResidue_antitone_right hb (hc n) hn

/-- Vanishing boundary residues also control every intervening good partial cell. -/
theorem radialResidue_remainder_tendsto_zero {c T : ℕ → ℝ}
    (hc : ∀ n, GoodHeight (c n)) (hT : ∀ n, GoodHeight (T n))
    (hmono : Monotone c) (hleft : ∀ n, c n ≤ T n) (hright : ∀ n, T n ≤ c (n + 1))
    (hlim : Tendsto (fun n => radialResidue (c 0) (c n)) atTop (𝓝 0)) :
    Tendsto (fun n => radialResidue (c n) (T n)) atTop (𝓝 0) := by
  have hlim' := hlim.comp (tendsto_add_atTop_nat 1)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (by simpa [Function.comp_def] using hlim') tendsto_const_nhds
  · intro n
    exact radialResidue_le_subwindow (hc 0) (hc n) (hT n) (hc (n + 1))
      (hmono (Nat.zero_le n)) (hright n)
  · intro n
    exact radialResidue_nonpos (hc n) (hT n) (hleft n)

end CriticalLinePhasor.DVP

#print axioms CriticalLinePhasor.DVP.radialResidue_telescope
#print axioms CriticalLinePhasor.DVP.radialResidue_cells_and_remainder
#print axioms CriticalLinePhasor.DVP.radialResidue_zero_iff_cells_zero
#print axioms CriticalLinePhasor.DVP.radialResidue_le_neg_pair
#print axioms CriticalLinePhasor.DVP.radialResidue_remainder_bounds
#print axioms CriticalLinePhasor.DVP.radial_boundary_eq_cells
#print axioms CriticalLinePhasor.DVP.radialResidue_eq_integrated_lift_gap
#print axioms CriticalLinePhasor.DVP.radialResidue_zero_of_boundary_limit
#print axioms CriticalLinePhasor.DVP.radialResidue_remainder_tendsto_zero
