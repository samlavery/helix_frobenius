import RequestProject.CPSFunctorialityUnification3D
import RequestProject.RamanujanLimit
import RequestProject.CatalanMoment

/-!
# Radial closure and Sato--Tate geometry on the three-dimensional CPS carrier

This file keeps both statements in native carrier coordinates.  The finite-place statement acts
on the ledger-normalized transverse phase block, while `RamanujanLimit` keeps the arithmetic radial
strand separate.  The archimedean statement acts on the strand exponent itself.
The Sato--Tate statement is lifted to an explicit unit-radius Archimedean helix, whose third
coordinate is a global coordinate and whose transverse trace has the Catalan/Fourier moments.
-/

open Complex Matrix
open scoped Real

namespace CriticalLinePhasor.GlobalHelix

/-- A raw arithmetic strand together with one rank-independent ceiling for every positive
symmetric-power transport of its helix and anti-helix legs.  No unit-radius field is present. -/
structure TowerCeilingStrand where
  value : ℂ
  value_ne_zero : value ≠ 0
  bound : ℝ
  top : ∀ r : ℕ, 1 ≤ r → ‖value ^ r‖ ≤ bound
  bottom : ∀ r : ℕ, 1 ≤ r → ‖(value⁻¹) ^ r‖ ≤ bound

/-- The arithmetic input delivered by an identified symmetric-power tower at one unramified
place.  `topSatake r` and `bottomSatake r` are the actual extreme Satake parameters of the
`r`th lift; the two identification fields say that they are the powers of the retained raw
rank-two strand.  The common bound is the rank-independent constituent bound.  No norm-one
field occurs in this structure. -/
structure ArithmeticSatakeTowerAtPrime where
  value : ℂ
  value_ne_zero : value ≠ 0
  topSatake : ℕ → ℂ
  bottomSatake : ℕ → ℂ
  topSatake_eq : ∀ r, topSatake r = value ^ r
  bottomSatake_eq : ∀ r, bottomSatake r = (value⁻¹) ^ r
  bound : ℝ
  topSatake_bound : ∀ r : ℕ, 1 ≤ r → ‖topSatake r‖ ≤ bound
  bottomSatake_bound : ∀ r : ℕ, 1 ≤ r → ‖bottomSatake r‖ ≤ bound

/-- The identified arithmetic tower, rather than a unitary phase shadow, constructs the raw
tower-ceiling strand consumed by the radial limit. -/
def ArithmeticSatakeTowerAtPrime.toTowerCeilingStrand
    (T : ArithmeticSatakeTowerAtPrime) : TowerCeilingStrand where
  value := T.value
  value_ne_zero := T.value_ne_zero
  bound := T.bound
  top := by
    intro r hr
    rw [← T.topSatake_eq r]
    exact T.topSatake_bound r hr
  bottom := by
    intro r hr
    rw [← T.bottomSatake_eq r]
    exact T.bottomSatake_bound r hr

/-- Radius one is derived from the actual extreme Satake parameters of every tower rung. -/
theorem ArithmeticSatakeTowerAtPrime.radius_one
    (T : ArithmeticSatakeTowerAtPrime) : ‖T.value‖ = 1 := by
  exact RamanujanLimit.strand_radius_one_of_tower_ceiling T.value_ne_zero
    T.toTowerCeilingStrand.top T.toTowerCeilingStrand.bottom

/-- The deprojected arithmetic strand block is an isometry after, and because, the identified
tower bounds have forced its retained radius to one. -/
theorem ArithmeticSatakeTowerAtPrime.strandBlock_isometry
    (T : ArithmeticSatakeTowerAtPrime) :
    (RamanujanLimit.strandBlock T.value)ᴴ *
        RamanujanLimit.strandBlock T.value = 1 :=
  RamanujanLimit.strandBlock_unitary_of_radius_one T.radius_one

/-- Every symmetric-power rung of a CPS prime phase and its inverse lies under the same unit
ceiling.  This is a statement about the transverse phase coordinate before scalar projection. -/
theorem unitaryPrimePhase_towerCeiling (alpha : UnitaryPrimePhase) (p : Nat.Primes) :
    (∀ r : ℕ, 1 ≤ r → ‖alpha.phase p ^ r‖ ≤ 1) ∧
      (∀ r : ℕ, 1 ≤ r → ‖(alpha.phase p)⁻¹ ^ r‖ ≤ 1) := by
  constructor <;> intro r _
  · rw [norm_pow, alpha.unit, one_pow]
  · rw [norm_pow, norm_inv, alpha.unit, inv_one, one_pow]

/-- The deprojected strand block of the CPS phase shadow is a transverse isometry, obtained by
feeding its complete tower orbit to the radial-limit theorem. -/
theorem unitaryPrimePhase_strandBlock_isometry (alpha : UnitaryPrimePhase) (p : Nat.Primes) :
    (RamanujanLimit.strandBlock (alpha.phase p))ᴴ *
        RamanujanLimit.strandBlock (alpha.phase p) = 1 := by
  have hne : alpha.phase p ≠ 0 := by
    intro h
    simpa [h] using alpha.unit p
  obtain ⟨htop, hbot⟩ := unitaryPrimePhase_towerCeiling alpha p
  exact RamanujanLimit.strandBlock_unitary_of_tower_ceiling hne htop hbot

/-- A real archimedean frequency written as its native, drift-free complex strand exponent. -/
noncomputable def archimedeanPhaseExponent (t : ℝ) : ℂ := (t : ℂ) * I

/-- Every rank multiple of the native archimedean phase exponent has zero radial rate. -/
theorem archimedeanPhaseExponent_towerCeiling (t : ℝ) :
    ∀ r : ℕ, 1 ≤ r → |((r : ℂ) * archimedeanPhaseExponent t).re| ≤ 0 := by
  intro r _
  simp [archimedeanPhaseExponent]

/-- The full archimedean strand profile is unit-modulus at every carrier height. -/
theorem archimedeanPhaseExponent_strand_unimodular (t y : ℝ) :
    ‖Complex.exp ((y : ℂ) * archimedeanPhaseExponent t)‖ = 1 := by
  exact RamanujanLimit.archimedean_strand_unimodular_of_tower_ceiling
    (archimedeanPhaseExponent_towerCeiling t) y

end CriticalLinePhasor.GlobalHelix

namespace CriticalLinePhasor.SatoTateCarrier3D

open MeasureTheory Set

/-- The unit-radius Archimedean helix carrying a Sato--Tate angle as its global coordinate. -/
noncomputable def point (theta : ℝ) : ℝ × ℝ × ℝ :=
  (Real.cos theta, Real.sin theta, theta)

/-- The third coordinate is the global coordinate map on the helix. -/
def globalCoordinate (x : ℝ × ℝ × ℝ) : ℝ := x.2.2

/-- The transverse trace read directly from the first carrier coordinate. -/
def trace (x : ℝ × ℝ × ℝ) : ℝ := 2 * x.1

/-- The global coordinate is a left inverse of the helix parametrization. -/
@[simp] theorem globalCoordinate_point (theta : ℝ) : globalCoordinate (point theta) = theta := rfl

/-- The transverse coordinates of every carrier point lie on the unit circle. -/
theorem transverse_radius_sq (theta : ℝ) :
    (point theta).1 ^ 2 + (point theta).2.1 ^ 2 = 1 := by
  exact Real.cos_sq_add_sin_sq theta

/-- The trace is the native transverse readout `2 cos theta`, with `theta` recovered by the global
coordinate rather than inserted by a separate chart. -/
theorem trace_point (theta : ℝ) :
    trace (point theta) = 2 * Real.cos (globalCoordinate (point theta)) := by
  rfl

/-- The normalized Sato--Tate angle density, kept on the global coordinate before it is lifted
to the carrier. -/
noncomputable def angleMeasure : Measure ℝ :=
  (volume.restrict (Icc (0 : ℝ) Real.pi)).withDensity
    (fun theta => ENNReal.ofReal ((2 / Real.pi) * Real.sin theta ^ 2))

/-- The density carried by the global coordinate has total mass one. -/
theorem angleMeasure_apply_univ : angleMeasure Set.univ = 1 := by
  let density : ℝ → ℝ := fun theta => (2 / Real.pi) * Real.sin theta ^ 2
  have hdensity_cont : Continuous density := by
    dsimp [density]
    fun_prop
  have hdensity_int : Integrable density (volume.restrict (Icc (0 : ℝ) Real.pi)) :=
    hdensity_cont.integrableOn_Icc
  have hdensity_nonneg : 0 ≤ᵐ[volume.restrict (Icc (0 : ℝ) Real.pi)] density :=
    Filter.Eventually.of_forall fun theta => mul_nonneg (by positivity) (sq_nonneg _)
  rw [angleMeasure, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
    ← ofReal_integral_eq_lintegral_ofReal hdensity_int hdensity_nonneg]
  have hmass : ∫ theta in Icc (0 : ℝ) Real.pi, density theta = 1 := by
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le Real.pi_pos.le]
    change (∫ theta in (0 : ℝ)..Real.pi,
      (2 / Real.pi) * Real.sin theta ^ 2) = 1
    rw [intervalIntegral.integral_const_mul]
    exact CatalanMoment.stFourierMoment_zero
  rw [hmass, ENNReal.ofReal_one]

noncomputable instance angleMeasure_isProbability : IsProbabilityMeasure angleMeasure :=
  ⟨angleMeasure_apply_univ⟩

/-- The Sato--Tate measure in native three-dimensional form is the pushforward of the angle
density onto the helix, not a measure introduced on a separate one-dimensional zero chart. -/
noncomputable def carrierMeasure : Measure (ℝ × ℝ × ℝ) :=
  Measure.map point angleMeasure

theorem continuous_point : Continuous point := by
  unfold point
  exact Real.continuous_cos.prodMk (Real.continuous_sin.prodMk continuous_id)

theorem continuous_globalCoordinate : Continuous globalCoordinate := by
  unfold globalCoordinate
  exact continuous_snd.comp continuous_snd

noncomputable instance carrierMeasure_isProbability : IsProbabilityMeasure carrierMeasure := by
  unfold carrierMeasure
  exact Measure.isProbabilityMeasure_map continuous_point.measurable.aemeasurable

/-- The global coordinate `S(t)` recovers the entire Sato--Tate angle measure from its native
three-dimensional carrier measure. -/
theorem map_globalCoordinate_carrierMeasure :
    Measure.map globalCoordinate carrierMeasure = angleMeasure := by
  rw [carrierMeasure, Measure.map_map continuous_globalCoordinate.measurable
    continuous_point.measurable]
  simpa only [Function.comp_def, globalCoordinate_point] using
    (Measure.map_id' (μ := angleMeasure))

/-- Even transverse trace moments on the 3D carrier are the Catalan numbers. -/
theorem traceMoment_even (m : ℕ) :
    (2 / Real.pi) *
        ∫ theta in (0 : ℝ)..Real.pi,
          trace (point theta) ^ (2 * m) * (point theta).2.1 ^ 2 =
      (Nat.centralBinom m : ℝ) / (m + 1) := by
  simpa [trace, point] using CatalanMoment.stMoment_even m

/-- Odd transverse trace moments on the 3D carrier vanish. -/
theorem traceMoment_odd (m : ℕ) :
    (2 / Real.pi) *
        ∫ theta in (0 : ℝ)..Real.pi,
          trace (point theta) ^ (2 * m + 1) * (point theta).2.1 ^ 2 = 0 := by
  simpa [trace, point] using CatalanMoment.stMoment_odd m

/-- Every Fourier moment of the 3D global-coordinate field is the Sato--Tate scalar moment. -/
theorem globalCoordinate_fourierMoment (d : ℤ) :
    (2 / Real.pi) *
        ∫ theta in (0 : ℝ)..Real.pi,
          Real.cos ((d : ℝ) * globalCoordinate (point theta)) * (point theta).2.1 ^ 2 =
      ((MomentLaw.stMoment d : ℚ) : ℝ) := by
  simpa [globalCoordinate, point] using CatalanMoment.stFourierMoment d

/-- The complete native 3D Sato--Tate geometry: global-coordinate recovery, unit transverse
radius, exact recovery of the Sato--Tate measure by `S(t)`, and the even, odd, and Fourier moment
laws on the same helix. -/
theorem geometry_unified (theta : ℝ) :
    globalCoordinate (point theta) = theta ∧
      (point theta).1 ^ 2 + (point theta).2.1 ^ 2 = 1 ∧
      (∀ m : ℕ,
        (2 / Real.pi) *
            ∫ u in (0 : ℝ)..Real.pi,
              trace (point u) ^ (2 * m) * (point u).2.1 ^ 2 =
          (Nat.centralBinom m : ℝ) / (m + 1)) ∧
      (∀ m : ℕ,
        (2 / Real.pi) *
            ∫ u in (0 : ℝ)..Real.pi,
              trace (point u) ^ (2 * m + 1) * (point u).2.1 ^ 2 = 0) ∧
      ∀ d : ℤ,
        (2 / Real.pi) *
            ∫ u in (0 : ℝ)..Real.pi,
              Real.cos ((d : ℝ) * globalCoordinate (point u)) * (point u).2.1 ^ 2 =
          ((MomentLaw.stMoment d : ℚ) : ℝ) := by
  exact ⟨globalCoordinate_point theta, transverse_radius_sq theta,
    traceMoment_even, traceMoment_odd, globalCoordinate_fourierMoment⟩

end CriticalLinePhasor.SatoTateCarrier3D

namespace CriticalLinePhasor

open MeasureTheory

/-- One theorem surface for the completed radial and Sato--Tate facts native to the CPS carrier.
The finite strand is not supplied as unitary input: a nonzero strand whose positive powers and
inverse powers lie below one rank-independent tower ceiling first has radius exactly one.  Its
block is therefore an isometry.  The same conclusion retains the drift-free Archimedean strand,
the unit-radius helix, recovery of the angle and its full measure by `S(t)`, and every Sato--Tate
Fourier moment. -/
theorem cpsRadialSatoTateGeometry3D_unified
    (strand : GlobalHelix.TowerCeilingStrand) (t y theta : ℝ) :
    ‖strand.value‖ = 1 ∧
      (RamanujanLimit.strandBlock strand.value)ᴴ *
        RamanujanLimit.strandBlock strand.value = 1 ∧
      ‖Complex.exp ((y : ℂ) * GlobalHelix.archimedeanPhaseExponent t)‖ = 1 ∧
      SatoTateCarrier3D.globalCoordinate (SatoTateCarrier3D.point theta) = theta ∧
      (SatoTateCarrier3D.point theta).1 ^ 2 +
          (SatoTateCarrier3D.point theta).2.1 ^ 2 = 1 ∧
      Measure.map SatoTateCarrier3D.globalCoordinate SatoTateCarrier3D.carrierMeasure =
        SatoTateCarrier3D.angleMeasure ∧
      SatoTateCarrier3D.angleMeasure Set.univ = 1 ∧
      ∀ d : ℤ,
        (2 / Real.pi) *
            ∫ u in (0 : ℝ)..Real.pi,
              Real.cos ((d : ℝ) *
                SatoTateCarrier3D.globalCoordinate (SatoTateCarrier3D.point u)) *
                  (SatoTateCarrier3D.point u).2.1 ^ 2 =
          ((MomentLaw.stMoment d : ℚ) : ℝ) := by
  have hradius := RamanujanLimit.strand_radius_one_of_tower_ceiling
    strand.value_ne_zero strand.top strand.bottom
  have hisometry := RamanujanLimit.strandBlock_unitary_of_tower_ceiling
    strand.value_ne_zero strand.top strand.bottom
  exact ⟨hradius, hisometry,
    GlobalHelix.archimedeanPhaseExponent_strand_unimodular t y,
    SatoTateCarrier3D.globalCoordinate_point theta,
    SatoTateCarrier3D.transverse_radius_sq theta,
    SatoTateCarrier3D.map_globalCoordinate_carrierMeasure,
    SatoTateCarrier3D.angleMeasure_apply_univ,
    SatoTateCarrier3D.globalCoordinate_fourierMoment⟩

end CriticalLinePhasor

#print axioms CriticalLinePhasor.GlobalHelix.unitaryPrimePhase_towerCeiling
#print axioms CriticalLinePhasor.GlobalHelix.ArithmeticSatakeTowerAtPrime.radius_one
#print axioms CriticalLinePhasor.GlobalHelix.ArithmeticSatakeTowerAtPrime.strandBlock_isometry
#print axioms CriticalLinePhasor.GlobalHelix.unitaryPrimePhase_strandBlock_isometry
#print axioms CriticalLinePhasor.GlobalHelix.archimedeanPhaseExponent_strand_unimodular
#print axioms CriticalLinePhasor.SatoTateCarrier3D.map_globalCoordinate_carrierMeasure
#print axioms CriticalLinePhasor.SatoTateCarrier3D.angleMeasure_apply_univ
#print axioms CriticalLinePhasor.SatoTateCarrier3D.geometry_unified
#print axioms CriticalLinePhasor.cpsRadialSatoTateGeometry3D_unified
