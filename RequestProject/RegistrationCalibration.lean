import RequestProject.RegistrationScale
import RequestProject.HelixRegistrationWarp

/-!
# Integer-level boundaries for the growing registry

Unfolded statement: using q(t)-1/2 as the input to the existing station
constructor places the unshifted clock theta(t)/pi+q(t) at n-1. Its unshifted
residual is then N(t)-n. The bank change in the master count identity survives
this constant shift exactly.

Expectation-free route A: `rw [regClock]` and subtract the constant in the
coercivity proof. Route B: `have hid := count_identity ...` and use the two
integer-level endpoint equations. Both routes are implemented below.

Searches: `rg -n -i 'station.*shift|shift.*station|boundary.*station|integer.*level|center.*strain|strain.*half|shifted.*strain|strain.*offset|level.*offset' RequestProject --glob '*.lean'`;
`rg -n 'tendsto.*atTop.*sub_const|atTop_sub_const|tendsto_atTop_add_const_right|tendsto_atTop_atTop|const_sub_atTop' .lake/packages/mathlib/Mathlib/Topology/Algebra/Order .lake/packages/mathlib/Mathlib/Order/Filter`.
-/

open Complex Filter Topology MeasureTheory
open scoped Interval
open CriticalLinePhasor.CarrierScale (theta)

namespace CriticalLinePhasor.ContourArgument

noncomputable def boundaryStrain (q : ℝ → ℝ) (t : ℝ) : ℝ := q t - 1 / 2

noncomputable def boundaryStation (q : ℝ → ℝ) (n : ℕ) : ℝ :=
  station (boundaryStrain q) n

theorem boundaryStrain_continuous {q : ℝ → ℝ} (hq : Continuous q) :
    Continuous (boundaryStrain q) := hq.sub continuous_const

theorem boundaryClock_tendsto {q : ℝ → ℝ}
    (hT : Tendsto (regClock q) atTop atTop) :
    Tendsto (regClock (boundaryStrain q)) atTop atTop := by
  rw [tendsto_atTop_atTop] at hT ⊢
  intro M
  obtain ⟨T, hT⟩ := hT (M + 1 / 2)
  refine ⟨T, fun t ht => ?_⟩
  have h := hT t ht
  dsimp [regClock, boundaryStrain] at h ⊢
  linarith

theorem boundaryStation_spec {q : ℝ → ℝ} (hq : Continuous q)
    (hT : Tendsto (regClock q) atTop atTop) {n : ℕ}
    (hn : regClock q 10 < (n : ℝ) - 1) :
    10 ≤ boundaryStation q n ∧
      regClock q (boundaryStation q n) = (n : ℝ) - 1 := by
  have hn' : regClock (boundaryStrain q) 10 < stationLevel n := by
    dsimp [regClock, boundaryStrain, stationLevel] at hn ⊢
    linarith
  obtain ⟨ha, hb⟩ := station_spec' (boundaryStrain_continuous hq) (boundaryClock_tendsto hT) hn'
  refine ⟨ha, ?_⟩
  dsimp [regClock, boundaryStrain, stationLevel, boundaryStation] at hb ⊢
  linarith

theorem boundaryStation_lt {q : ℝ → ℝ} (hq : Continuous q)
    (hT : Tendsto (regClock q) atTop atTop) {n : ℕ}
    (hn : regClock q 10 < (n : ℝ) - 1) :
    boundaryStation q n < boundaryStation q (n + 1) := by
  apply station_lt' (boundaryStrain_continuous hq) (boundaryClock_tendsto hT)
  dsimp [regClock, boundaryStrain, stationLevel] at hn ⊢
  linarith

theorem boundary_resid_integer {q : ℝ → ℝ} (hq : Continuous q)
    (hT : Tendsto (regClock q) atTop atTop) {n : ℕ}
    (hn : regClock q 10 < (n : ℝ) - 1) :
    resid q (boundaryStation q n) =
      (stripZeroCountMult (boundaryStation q n) : ℝ) - n := by
  have hs := (boundaryStation_spec hq hT hn).2
  dsimp [resid, regClock] at hs ⊢
  linarith

/-- The complete signed defect, evaluated at one fixed Riesz scale. -/
noncomputable def registrationDefect (Lf : ℝ → ℝ) (a b : ℝ) : ℝ :=
  (1 / Real.pi) * (∫ t in a..b, rieszRemainder (Lf a) t) + boundaryTerm (Lf a) a b
    - (rieszStrain (Lf b) b - rieszStrain (Lf a) b)

theorem calibrated_registry_count {c : ℝ} (hc : 0 < c) (hc1 : c < 1) {n : ℕ}
    (hn : regClock (registryStrain c) 10 < (n : ℝ) - 1) :
    (bandCountMult (boundaryStation (registryStrain c) n)
      (boundaryStation (registryStrain c) (n + 1)) : ℝ) =
    1 + registrationDefect (logScale c) (boundaryStation (registryStrain c) n)
      (boundaryStation (registryStrain c) (n + 1)) := by
  have hq := registryStrain_continuous hc
  have hT := registry_regClock_tendsto hc hc1
  have hn' : regClock (registryStrain c) 10 < ((n + 1 : ℕ) : ℝ) - 1 := by
    push_cast
    linarith
  obtain ⟨ha, hGa⟩ := boundaryStation_spec hq hT hn
  obtain ⟨hb, hGb⟩ := boundaryStation_spec hq hT hn'
  have hab := (boundaryStation_lt hq hT hn).le
  have hid := count_identity (logScale_pos hc (boundaryStation (registryStrain c) n))
    (by linarith : 0 < boundaryStation (registryStrain c) n) hab
  rw [hid]
  change theta (boundaryStation (registryStrain c) n) / Real.pi +
    rieszStrain (logScale c (boundaryStation (registryStrain c) n))
      (boundaryStation (registryStrain c) n) = (n : ℝ) - 1 at hGa
  change theta (boundaryStation (registryStrain c) (n + 1)) / Real.pi +
    rieszStrain (logScale c (boundaryStation (registryStrain c) (n + 1)))
      (boundaryStation (registryStrain c) (n + 1)) = ((n + 1 : ℕ) : ℝ) - 1 at hGb
  dsimp [registrationDefect]
  push_cast at hGb
  have hdiv (a b : ℝ) : (theta b - theta a) / Real.pi =
      theta b / Real.pi - theta a / Real.pi := by ring
  rw [hdiv]
  linarith

/-- Native multiplicity registration relative to the same height-dependent bank. -/
noncomputable def nativeRegistryResidual (Lf : ℝ → ℝ) (t : ℝ) : ℝ :=
  ResidueJump.Smult t - rieszStrain (Lf t) t

/-- Exact transfer from the Riesz formula to the unwrapped off-line census.
This retains every multiplicity and allows any number of zeros in the interval. -/
theorem offLine_increment_eq_registrationDefect_sub_native {Lf : ℝ → ℝ} {a b : ℝ}
    (hLa : 0 < Lf a) (ha : GoodHeight a) (hb : GoodHeight b) (hab : a ≤ b) :
    (offLineStripZeroCountMult b : ℝ) - (offLineStripZeroCountMult a : ℝ) =
      registrationDefect Lf a b -
        (nativeRegistryResidual Lf b - nativeRegistryResidual Lf a) := by
  have hS := S_identity hLa ha hb hab
  rw [classicalSContour_eq_Smult_add_offLine ha,
    classicalSContour_eq_Smult_add_offLine hb] at hS
  dsimp [registrationDefect, nativeRegistryResidual]
  linarith

end CriticalLinePhasor.ContourArgument

#print axioms CriticalLinePhasor.ContourArgument.boundaryStation_spec
#print axioms CriticalLinePhasor.ContourArgument.boundary_resid_integer
#print axioms CriticalLinePhasor.ContourArgument.calibrated_registry_count
#print axioms CriticalLinePhasor.ContourArgument.offLine_increment_eq_registrationDefect_sub_native
