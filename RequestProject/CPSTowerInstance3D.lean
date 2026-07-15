import RequestProject.CPSTowerAssembly3D

/-!
# The tower package instantiated on the twisted symmetric-power bank

This file builds the carrier state space that discharges every field of `TowerThetaPackage` on
genuine Satake-bank data, firing the tower landing `TowerThetaPackage.landing` — full
`GL(n, K)` invariance — for every rank `r`, every unitary prime phase `α`, and every unitary
Satake family type `κ`.

**The mechanism: two charts welded at the self-dual point.**  A state is a position vector on the
finite carrier plane together with a Satake configuration.  The readout is chart-branching: on the
hyperplane (position coordinate `i₀` zero) it reads the **primal** bank at the self-dual point;
off the hyperplane it reads the **contragredient** bank there.  General-linear moves genuinely
cross the chart boundary, so invariance of the readout is exactly the statement that the two
charts agree — `cpsDualPair_selfDualPointIdentity`, the payload reflection evaluated at the weld.

**Non-vacuity is compiled, not prose.**  `chartReadout_not_invariant_of_ne` shows the same
construction on any chart pair whose values differ at some configuration is *not* invariant: a
single unit transvection crosses the weld and separates the values.  The landing therefore
genuinely consumes the reflection.  This is the difference from the finite model of
`CPSLatticeInstance3D`, whose invariance held for arbitrary functions by reindexing; here the
invariance fails without the arithmetic identity.  The readout is also non-constant across
configurations.

Register: the conclusion is carrier readout invariance for the bank states; the classical
discrimination lives in the identification layer as recorded in the manuscript.  This file does
not assume or prove RH/GRH.
-/

open Matrix
open scoped Classical

namespace CriticalLinePhasor.ThreeDConverse

section ChartCarrier

variable {n K : Type*} [Fintype n] [DecidableEq n] [Field K]

/-- A tower state: a position vector on the finite carrier plane together with a configuration
drawn from an arbitrary type `B` (instantiated below with the unitary Satake families). -/
abbrev TowerState (n K B : Type*) := (n → K) × B

instance towerStateSMul (B : Type*) :
    SMul (Matrix.GeneralLinearGroup n K) (TowerState n K B) where
  smul g x := ((g : Matrix n n K).mulVec x.1, x.2)

@[simp] lemma towerState_smul_fst {B : Type*}
    (g : Matrix.GeneralLinearGroup n K) (x : TowerState n K B) :
    (g • x).1 = (g : Matrix n n K).mulVec x.1 := rfl

@[simp] lemma towerState_smul_snd {B : Type*}
    (g : Matrix.GeneralLinearGroup n K) (x : TowerState n K B) :
    (g • x).2 = x.2 := rfl

/-- The general linear group moves the position and carries the configuration along. -/
instance towerStateMulAction (B : Type*) :
    MulAction (Matrix.GeneralLinearGroup n K) (TowerState n K B) where
  one_smul x := by
    refine Prod.ext ?_ rfl
    show ((1 : Matrix.GeneralLinearGroup n K) : Matrix n n K).mulVec x.1 = x.1
    simp
  mul_smul g h x := by
    refine Prod.ext ?_ rfl
    show ((g * h : Matrix.GeneralLinearGroup n K) : Matrix n n K).mulVec x.1 =
      (g : Matrix n n K).mulVec ((h : Matrix n n K).mulVec x.1)
    rw [Units.val_mul, Matrix.mulVec_mulVec]

/-- The two-chart readout attached to a pair of configuration readings: the `P`-chart on the
`i₀`-hyperplane, the `D`-chart off it. -/
noncomputable def chartReadout (i₀ : n) {B : Type*} (P D : B → ℂ)
    (x : TowerState n K B) : ℂ :=
  if x.1 i₀ = 0 then P x.2 else D x.2

/-- **The compiled falsifier.**  If the two charts disagree at some configuration, the chart
readout is not invariant: a single unit transvection crosses the weld and separates the values.
The tower landing below therefore genuinely consumes the chart-agreement identity. -/
theorem chartReadout_not_invariant_of_ne
    {B : Type*} (i₀ j₀ : n) (hne : i₀ ≠ j₀) (P D : B → ℂ) (b : B)
    (hPD : P b ≠ D b) :
    ∃ (g : Matrix.GeneralLinearGroup n K) (x : TowerState n K B),
      chartReadout i₀ P D (g • x) ≠ chartReadout i₀ P D x := by
  refine ⟨transvectionGL i₀ j₀ hne (1 : K), ((Pi.single j₀ (1 : K) : n → K), b), ?_⟩
  have hbase : ((Pi.single j₀ (1 : K) : n → K)) i₀ = 0 := by
    simp [Pi.single_apply, hne]
  have hmoved :
      ((transvectionGL i₀ j₀ hne (1 : K) : Matrix n n K).mulVec
        (Pi.single j₀ (1 : K))) i₀ = 1 := by
    have hcoe : (transvectionGL i₀ j₀ hne (1 : K) : Matrix n n K) =
        Matrix.transvection i₀ j₀ (1 : K) := rfl
    rw [hcoe]
    simp [Matrix.mulVec_single, Matrix.transvection, Matrix.add_apply,
      Matrix.one_apply_ne hne, Matrix.single_apply_same, Matrix.col_apply,
      MulOpposite.op_one]
  have hmove_readout :
      chartReadout i₀ P D
        (transvectionGL i₀ j₀ hne (1 : K) • ((Pi.single j₀ 1, b) : TowerState n K B)) =
        D b := by
    unfold chartReadout
    simp only [towerState_smul_fst, towerState_smul_snd, hmoved]
    rw [if_neg one_ne_zero]
  have hbase_readout :
      chartReadout i₀ P D ((Pi.single j₀ 1, b) : TowerState n K B) = P b := by
    unfold chartReadout
    rw [if_pos hbase]
  rw [hmove_readout, hbase_readout]
  exact fun h => hPD h.symm

end ChartCarrier

section BankInstance

variable {n K : Type*} [Fintype n] [DecidableEq n] [Field K] [Finite K]
variable {κ : Type*} [Fintype κ]

/-- The tower chart readout on genuine bank data: primal bank at the self-dual point on the
hyperplane chart, contragredient bank off it. -/
noncomputable def towerChartReadout (i₀ : n) (r : ℕ) (α : GlobalHelix.UnitaryPrimePhase) :
    TowerState n K (GlobalHelix.UnitarySatakeFamily κ) → ℂ :=
  chartReadout i₀
    (fun τ => GlobalHelix.cpsPrimal3DBankReadout r α τ 1)
    (fun τ => GlobalHelix.cpsDual3DBankReadout r α τ 1)

/-- **Chart agreement at the weld.**  The two charts read the same value — this is the payload
reflection at the self-dual point, and it is the entire arithmetic content of the invariance. -/
theorem towerChartReadout_eq (i₀ : n) (r : ℕ) (α : GlobalHelix.UnitaryPrimePhase)
    (x : TowerState n K (GlobalHelix.UnitarySatakeFamily κ)) :
    towerChartReadout i₀ r α x = GlobalHelix.cpsDual3DBankReadout r α x.2 1 := by
  unfold towerChartReadout chartReadout
  split
  · exact cpsDualPair_selfDualPointIdentity r α x.2
  · rfl

/-- The half-weight radial factor carried by the profiles. -/
noncomputable def radialHalf (t : ℝ) : ℂ := ((t ^ (-(2⁻¹ : ℝ)) : ℝ) : ℂ)

lemma radialHalf_one : radialHalf 1 = 1 := by
  simp [radialHalf, Real.one_rpow]

lemma radialHalf_one_div {t : ℝ} (ht : 0 < t) :
    radialHalf (1 / t) = (t : ℂ) * radialHalf t := by
  unfold radialHalf
  rw [← Complex.ofReal_mul]
  congr 1
  have hr : t * t ^ (-(2⁻¹ : ℝ)) = t ^ (1 + -(2⁻¹ : ℝ)) := by
    rw [Real.rpow_add ht, Real.rpow_one]
  rw [hr, one_div, Real.inv_rpow ht.le, ← Real.rpow_neg ht.le, neg_neg]
  norm_num

/-- The tower package on the bank chart carrier: profiles are the character twists of the orbit
readouts weighted by the half-weight radial factor; the reflection field is discharged by chart
agreement (the payload identity), the identification fields definitionally. -/
noncomputable def towerBankPackage (i₀ : n) (r : ℕ) (α : GlobalHelix.UnitaryPrimePhase) :
    TowerThetaPackage n K K (TowerState n K (GlobalHelix.UnitarySatakeFamily κ)) where
  readout := towerChartReadout i₀ r α
  lift := id
  lift_zero := rfl
  lift_one := rfl
  hdiag := fun D hD x => by
    simp only [towerChartReadout_eq, towerState_smul_snd]
  primal := fun i j hij x character t =>
    finiteAbelianTwistReadout K
      (fun c => towerChartReadout i₀ r α (transvectionGL i j hij (id (c + 1)) • x)) character *
      radialHalf t
  dual := fun i j hij x character t =>
    finiteAbelianTwistReadout K
      (fun c => towerChartReadout i₀ r α (transvectionGL i j hij (id c) • x)) character *
      radialHalf t
  reflection := fun i j hij x character {t} ht => by
    have hcell :
        (fun c : K => towerChartReadout i₀ r α (transvectionGL i j hij (id (c + 1)) • x)) =
          (fun c : K => towerChartReadout i₀ r α (transvectionGL i j hij (id c) • x)) := by
      funext c
      simp only [towerChartReadout_eq, towerState_smul_snd]
    simp only [hcell, radialHalf_one_div ht]
    ring
  primal_readout := fun i j hij x character => by
    simp only [radialHalf_one, mul_one]
  dual_readout := fun i j hij x character => by
    simp only [radialHalf_one, mul_one]

/-- **The tower landing on genuine bank data.**  Full `GL(n, K)` invariance of the two-chart bank
readout, for every rank, prime phase, and Satake family type — fired through
`TowerThetaPackage.landing`, consuming the payload reflection at the weld. -/
theorem towerBankInstance_landing (i₀ : n) (r : ℕ) (α : GlobalHelix.UnitaryPrimePhase)
    (g : Matrix.GeneralLinearGroup n K)
    (x : TowerState n K (GlobalHelix.UnitarySatakeFamily κ)) :
    towerChartReadout i₀ r α (g • x) = towerChartReadout i₀ r α x :=
  (towerBankPackage (κ := κ) i₀ r α).landing g x

end BankInstance

end CriticalLinePhasor.ThreeDConverse

#print axioms CriticalLinePhasor.ThreeDConverse.chartReadout_not_invariant_of_ne
#print axioms CriticalLinePhasor.ThreeDConverse.towerChartReadout_eq
#print axioms CriticalLinePhasor.ThreeDConverse.towerBankPackage
#print axioms CriticalLinePhasor.ThreeDConverse.towerBankInstance_landing
