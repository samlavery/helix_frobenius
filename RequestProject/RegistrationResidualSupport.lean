import RequestProject.PrimeStrain
import RequestProject.RegistrationDC

/-!
# Verified steps for the station-discharge drafts

Unfolded targets: first crossings lie below a supplied upper crossing; the exact
residual at a good height is S(T) minus the strain; the adjacent residual difference
is the integer gap count minus one. Thus a strict unit bound on adjacent residuals
closes each gap count separately.

Expectation-free strategy A: `rw [resid_station]` and use integer discreteness.
Strategy B: `rw [stripZeroCountMult_eq_S]` and retain the exact S increment.
Both expansions are proved below. The remaining strict bound is a draft leaf.

Searches: `rg -n -i 'station.*(le|upper|below)|resid.*(goodHeight|classicalS|step|adjacent)'
RequestProject --glob '*.lean'`; Mathlib searches for `csInf_le`,
`intermediate_value_Icc`, `int.*abs.*lt_one`, `abs.*int.*lt_one`, and `strictMono.*bddBelow`.
-/

open Complex Filter Topology Set

namespace CriticalLinePhasor.ContourArgument

theorem station_le_of_level_le {strain : ℝ → ℝ} (hs : Continuous strain)
    {n : ℕ} {T : ℝ} (hT : 10 ≤ T)
    (hn : regClock strain 10 < stationLevel n)
    (hupper : stationLevel n ≤ regClock strain T) : station strain n ≤ T := by
  obtain ⟨u, hu, hGu⟩ := intermediate_value_Icc hT
    (regClock_continuous hs).continuousOn ⟨hn.le, hupper⟩
  exact (csInf_le (station_set_bddBelow strain n) ⟨hu.1, hGu⟩).trans hu.2

theorem primeStation_le_58_of_level_le (X : ℕ) {n : ℕ}
    (hn : regClock (primeStrain X) 10 < stationLevel n)
    (hupper : stationLevel n ≤ regClock (primeStrain X) 58) : primeStation X n ≤ 58 :=
  station_le_of_level_le (primeStrain_continuous X) (by norm_num) hn hupper

theorem resid_eq_classicalS_sub (strain : ℝ → ℝ) {T : ℝ} (hT : GoodHeight T) :
    resid strain T = classicalSContour hT - strain T := by
  rw [resid, stripZeroCountMult_eq_S hT]
  ring

theorem adjacent_resid_eq_band_sub_one {strain : ℝ → ℝ} {B : ℝ}
    (hs : Continuous strain) (hB : ∀ t, |strain t| ≤ B) {n : ℕ}
    (hn : regClock strain 10 < stationLevel n) :
    resid strain (station strain (n + 1)) - resid strain (station strain n) =
      (bandCountMult (station strain n) (station strain (n + 1)) : ℝ) - 1 := by
  have hn' : regClock strain 10 < stationLevel (n + 1) := by
    rw [stationLevel_succ]
    linarith
  rw [resid_station hs hB hn', resid_station hs hB hn]
  have hc := bandCountMult_add (station_lt hs hB hn).le
  have hcr : (bandCountMult (station strain n) (station strain (n + 1)) : ℝ) +
      stripZeroCountMult (station strain n) = stripZeroCountMult (station strain (n + 1)) := by
    exact_mod_cast hc
  push_cast
  linarith

theorem onePerGap_of_adjacent_resid {strain : ℝ → ℝ} {B : ℝ}
    (hs : Continuous strain) (hB : ∀ t, |strain t| ≤ B) {n₀ : ℕ}
    (hn₀ : regClock strain 10 < stationLevel n₀)
    (hstep : ∀ n, n₀ ≤ n →
      |resid strain (station strain (n + 1)) - resid strain (station strain n)| < 1) :
    OnePerGap (fun k => station strain (n₀ + k)) where
  mono := station_strictMono hs hB hn₀
  unbounded := station_tendsto hs hB hn₀
  one := by
    intro k
    have hn := lt_of_lt_of_le hn₀ (stationLevel_mono (Nat.le_add_right n₀ k))
    have h := hstep (n₀ + k) (Nat.le_add_right n₀ k)
    rw [adjacent_resid_eq_band_sub_one hs hB hn] at h
    have hi : (bandCountMult (station strain (n₀ + k))
        (station strain (n₀ + k + 1)) : ℤ) = 1 := by
      apply int_eq_of_abs_sub_lt_one
      exact_mod_cast h
    have hi' : bandCountMult (station strain (n₀ + k))
        (station strain (n₀ + k + 1)) = 1 := by exact_mod_cast hi
    simpa only [Nat.add_assoc] using hi'

/-- A single strict adjacent-residual inequality supplies a single exact count. -/
theorem prime_gap_count_of_adjacent_resid (X : ℕ) {n : ℕ}
    (hn : regClock (primeStrain X) 10 < stationLevel n)
    (hstep : |resid (primeStrain X) (primeStation X (n + 1)) -
      resid (primeStrain X) (primeStation X n)| < 1) :
    bandCountMult (primeStation X n) (primeStation X (n + 1)) = 1 := by
  rw [primeStation, primeStation,
    adjacent_resid_eq_band_sub_one (primeStrain_continuous X) (abs_primeStrain_le X) hn] at hstep
  have hi : (bandCountMult (primeStation X n) (primeStation X (n + 1)) : ℤ) = 1 := by
    apply int_eq_of_abs_sub_lt_one
    exact_mod_cast hstep
  exact_mod_cast hi

end CriticalLinePhasor.ContourArgument

#print axioms CriticalLinePhasor.ContourArgument.primeStation_le_58_of_level_le
#print axioms CriticalLinePhasor.ContourArgument.resid_eq_classicalS_sub
#print axioms CriticalLinePhasor.ContourArgument.adjacent_resid_eq_band_sub_one
#print axioms CriticalLinePhasor.ContourArgument.onePerGap_of_adjacent_resid
#print axioms CriticalLinePhasor.ContourArgument.prime_gap_count_of_adjacent_resid
