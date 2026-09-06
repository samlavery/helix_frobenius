import RequestProject.OnePerGap
import RequestProject.DVPGramCells
import RequestProject.StClockJumpLaw

/-!
# The registration stations and the residual law (ledger 601)

The registration operator's spectrum (HP_PROGRAM §1) is the station sequence
`ϑ(t_n)/π + 3/2 + Ŝ(t_n) = n`, with `Ŝ` the prime-forced strain. For ANY continuous bounded strain
this file defines the stations as the first crossings above height `10` of the levels `n − 3/2` by the
registration clock `G = ϑ/π + Ŝ` (the compiled floor `clockRate ≥ 1/10` above `10` makes `G` unbounded,
so the crossings exist by the intermediate value theorem), and proves:

* `station_spec`, `station_lt`, `station_tendsto`: the stations exist, are strictly increasing and
  unbounded, for every level above `G(10)`;
* `resid_station`: at a station the residual `R(t) = N(t) − 1 − ϑ(t)/π − Ŝ(t)` equals
  `N(t_n) − n + ½` EXACTLY (the DC: no estimate);
* `bandCountMult_add`: the gap count is the difference of the strip counts;
* **`onePerGap_of_resid`**: if the residual at the stations never drifts by a full unit from its
  value at the first station, every gap holds exactly one zero;
* **`nontrivialZeros_online_of_resid`**: hence RH (with the first station at or below `58`, the
  compiled ladder covering the range beneath), and simplicity of every zero above it.

The residual law `|R(t_n) − R(t_{n₀})| < 1` is the registry's residual tail law in count form: the
true `S` minus the prime-forced strain, sampled at the stations, stays inside a unit band. Measured
(att158/167/169): the stations register bijectively with maximum residual 0.31–0.38 spacings.
-/

open Complex Finset Filter Topology Set
open CriticalLinePhasor.CarrierScale (theta clockRate theta_continuous continuous_clockRate)

namespace CriticalLinePhasor.ContourArgument

/-! ## 1. The registration clock with strain -/

/-- `G(t) = ϑ(t)/π + Ŝ(t)`. -/
noncomputable def regClock (strain : ℝ → ℝ) (t : ℝ) : ℝ := theta t / Real.pi + strain t

theorem regClock_continuous {strain : ℝ → ℝ} (hs : Continuous strain) :
    Continuous (regClock strain) :=
  (theta_continuous.div_const _).add hs

/-- `ϑ` grows at least linearly above `10` (compiled floor `clockRate ≥ 1/10`). -/
theorem theta_growth {t : ℝ} (ht : 10 ≤ t) : (t - 10) / 10 ≤ theta t - theta 10 := by
  rw [CriticalLinePhasor.ResidueJump.theta_sub_theta]
  have h : ∫ u in (10:ℝ)..t, (1 / 10 : ℝ) ≤ ∫ u in (10:ℝ)..t, clockRate u := by
    apply intervalIntegral.integral_mono_on ht intervalIntegrable_const
      (continuous_clockRate.intervalIntegrable _ _)
    intro u hu
    exact CriticalLinePhasor.DVP.clockRate_floor hu.1
  rw [intervalIntegral.integral_const, smul_eq_mul] at h
  linarith

/-- The registration clock is unbounded above for any bounded strain. -/
theorem regClock_tendsto {strain : ℝ → ℝ} {B : ℝ} (hB : ∀ t, |strain t| ≤ B) :
    Tendsto (regClock strain) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro M
  refine ⟨max 10 (10 + 10 * (Real.pi * (M + B) - theta 10)), fun t ht => ?_⟩
  have ht10 : 10 ≤ t := le_trans (le_max_left _ _) ht
  have ht2 : 10 + 10 * (Real.pi * (M + B) - theta 10) ≤ t := le_trans (le_max_right _ _) ht
  have hg := theta_growth ht10
  have hsB : -B ≤ strain t := by
    have := hB t
    rw [abs_le] at this
    exact this.1
  have hπ := Real.pi_pos
  have hθ : Real.pi * (M + B) ≤ theta t := by linarith
  unfold regClock
  have : M + B ≤ theta t / Real.pi := by
    rw [le_div_iff₀ hπ]
    linarith
  linarith

/-! ## 2. The stations -/

/-- The level of the `n`-th station: `n − 3/2`. -/
noncomputable def stationLevel (n : ℕ) : ℝ := (n : ℝ) - 3 / 2

/-- The `n`-th station: the first height `≥ 10` at which the clock reaches level `n − 3/2`. -/
noncomputable def station (strain : ℝ → ℝ) (n : ℕ) : ℝ :=
  sInf {t : ℝ | 10 ≤ t ∧ regClock strain t = stationLevel n}

theorem station_exists {strain : ℝ → ℝ} {B : ℝ} (hs : Continuous strain) (hB : ∀ t, |strain t| ≤ B)
    {n : ℕ} (hn : regClock strain 10 < stationLevel n) :
    ∃ t, 10 ≤ t ∧ regClock strain t = stationLevel n := by
  obtain ⟨T, hT⟩ := (tendsto_atTop_atTop.1 (regClock_tendsto hB)) (stationLevel n)
  have hb : stationLevel n ≤ regClock strain (max 10 T) := hT _ (le_max_right _ _)
  have hmem : stationLevel n ∈ Icc (regClock strain 10) (regClock strain (max 10 T)) := ⟨hn.le, hb⟩
  obtain ⟨t, ht, hGt⟩ := intermediate_value_Icc (le_max_left (10:ℝ) T)
    (regClock_continuous hs).continuousOn hmem
  exact ⟨t, ht.1, hGt⟩

theorem station_set_closed {strain : ℝ → ℝ} (hs : Continuous strain) (n : ℕ) :
    IsClosed {t : ℝ | 10 ≤ t ∧ regClock strain t = stationLevel n} :=
  isClosed_Ici.inter (isClosed_eq (regClock_continuous hs) continuous_const)

theorem station_set_bddBelow (strain : ℝ → ℝ) (n : ℕ) :
    BddBelow {t : ℝ | 10 ≤ t ∧ regClock strain t = stationLevel n} :=
  ⟨10, fun _ ht => ht.1⟩

/-- The station exists, sits above `10`, and is a crossing of its level. -/
theorem station_spec {strain : ℝ → ℝ} {B : ℝ} (hs : Continuous strain) (hB : ∀ t, |strain t| ≤ B)
    {n : ℕ} (hn : regClock strain 10 < stationLevel n) :
    10 ≤ station strain n ∧ regClock strain (station strain n) = stationLevel n :=
  (station_set_closed hs n).csInf_mem (station_exists hs hB hn) (station_set_bddBelow strain n)

theorem stationLevel_succ (n : ℕ) : stationLevel (n + 1) = stationLevel n + 1 := by
  unfold stationLevel
  push_cast
  ring

theorem stationLevel_mono {n m : ℕ} (h : n ≤ m) : stationLevel n ≤ stationLevel m := by
  unfold stationLevel
  have : (n : ℝ) ≤ m := by exact_mod_cast h
  linarith

/-- Consecutive stations are strictly ordered. -/
theorem station_lt {strain : ℝ → ℝ} {B : ℝ} (hs : Continuous strain) (hB : ∀ t, |strain t| ≤ B)
    {n : ℕ} (hn : regClock strain 10 < stationLevel n) :
    station strain n < station strain (n + 1) := by
  have hn' : regClock strain 10 < stationLevel (n + 1) := by
    rw [stationLevel_succ]; linarith
  obtain ⟨h1, hG1⟩ := station_spec hs hB hn
  obtain ⟨h2, hG2⟩ := station_spec hs hB hn'
  by_contra hle
  simp only [not_lt] at hle
  have hmem : stationLevel n ∈ Icc (regClock strain 10) (regClock strain (station strain (n + 1))) :=
    ⟨hn.le, by rw [hG2, stationLevel_succ]; linarith⟩
  obtain ⟨s, hs', hGs⟩ := intermediate_value_Icc h2 (regClock_continuous hs).continuousOn hmem
  have hle' : station strain n ≤ s := csInf_le (station_set_bddBelow strain n) ⟨hs'.1, hGs⟩
  have heq : station strain n = station strain (n + 1) := le_antisymm (hle'.trans hs'.2) hle
  rw [heq, hG2, stationLevel_succ] at hG1
  linarith

theorem station_strictMono {strain : ℝ → ℝ} {B : ℝ} (hs : Continuous strain)
    (hB : ∀ t, |strain t| ≤ B) {n₀ : ℕ} (hn₀ : regClock strain 10 < stationLevel n₀) :
    StrictMono (fun k => station strain (n₀ + k)) := by
  apply strictMono_nat_of_lt_succ
  intro k
  have : regClock strain 10 < stationLevel (n₀ + k) :=
    lt_of_lt_of_le hn₀ (stationLevel_mono (by omega))
  show station strain (n₀ + k) < station strain (n₀ + (k + 1))
  rw [show n₀ + (k + 1) = n₀ + k + 1 by omega]
  exact station_lt hs hB this

/-- The stations are unbounded. -/
theorem station_tendsto {strain : ℝ → ℝ} {B : ℝ} (hs : Continuous strain)
    (hB : ∀ t, |strain t| ≤ B) {n₀ : ℕ} (hn₀ : regClock strain 10 < stationLevel n₀) :
    Tendsto (fun k => station strain (n₀ + k)) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro M
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := (10:ℝ)) (b := max 10 M)).exists_bound_of_continuousOn
    (regClock_continuous hs).continuousOn
  refine ⟨⌈K⌉₊ + 2, fun k hk => ?_⟩
  have hn : regClock strain 10 < stationLevel (n₀ + k) :=
    lt_of_lt_of_le hn₀ (stationLevel_mono (by omega))
  obtain ⟨h10, hG⟩ := station_spec hs hB hn
  by_contra hlt
  simp only [not_le] at hlt
  have hmem : station strain (n₀ + k) ∈ Icc (10:ℝ) (max 10 M) :=
    ⟨h10, hlt.le.trans (le_max_right _ _)⟩
  have hbound := hK _ hmem
  rw [hG, Real.norm_eq_abs] at hbound
  have hlev : (K : ℝ) + 1 / 2 ≤ stationLevel (n₀ + k) := by
    unfold stationLevel
    have h1 : (⌈K⌉₊ : ℝ) + 2 ≤ ((n₀ + k : ℕ) : ℝ) := by
      have : ⌈K⌉₊ + 2 ≤ n₀ + k := by omega
      exact_mod_cast this
    have h2 : K ≤ (⌈K⌉₊ : ℝ) := Nat.le_ceil K
    linarith
  have := (abs_le.1 hbound).2
  linarith

/-! ## 3. The residual and the count -/

/-- The residual `R(t) = N(t) − 1 − ϑ(t)/π − Ŝ(t)`: the strip count against the strained clock. -/
noncomputable def resid (strain : ℝ → ℝ) (t : ℝ) : ℝ :=
  (stripZeroCountMult t : ℝ) - 1 - theta t / Real.pi - strain t

/-- **At a station the residual is `N(t_n) − n + ½` exactly.** -/
theorem resid_station {strain : ℝ → ℝ} {B : ℝ} (hs : Continuous strain) (hB : ∀ t, |strain t| ≤ B)
    {n : ℕ} (hn : regClock strain 10 < stationLevel n) :
    resid strain (station strain n) = (stripZeroCountMult (station strain n) : ℝ) - n + 1 / 2 := by
  have h := (station_spec hs hB hn).2
  unfold regClock stationLevel at h
  unfold resid
  linarith

theorem stripZeroFinset_mono {a b : ℝ} (h : a ≤ b) : stripZeroFinset a ⊆ stripZeroFinset b := by
  intro ρ hρ
  rw [mem_stripZeroFinset_iff'] at hρ ⊢
  exact ⟨hρ.1, hρ.2.1, hρ.2.2.trans h⟩

/-- The gap count is the difference of the strip counts. -/
theorem bandCountMult_add {a b : ℝ} (h : a ≤ b) :
    bandCountMult a b + stripZeroCountMult a = stripZeroCountMult b := by
  unfold bandCountMult stripZeroCountMult
  rw [← Finset.sum_filter_add_sum_filter_not (stripZeroFinset b) (fun ρ => a < ρ.im)]
  congr 1
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext ρ
  rw [Finset.mem_filter, mem_stripZeroFinset_iff', mem_stripZeroFinset_iff']
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, h2, h3.trans h⟩, not_lt.2 h3⟩
  · rintro ⟨⟨h1, h2, _⟩, h4⟩
    exact ⟨h1, h2, not_lt.1 h4⟩

/-- An integer within distance `< 1` of another integer equals it. -/
theorem int_eq_of_abs_sub_lt_one {a b : ℤ} (h : |((a : ℝ)) - b| < 1) : a = b := by
  have h' : |((a - b : ℤ) : ℝ)| < 1 := by push_cast; exact h
  rw [← Int.cast_abs] at h'
  have h'' : |a - b| < 1 := by exact_mod_cast h'
  have := Int.abs_lt_one_iff.1 h''
  linarith

/-- **The residual law gives one zero per gap.** -/
theorem onePerGap_of_resid {strain : ℝ → ℝ} {B : ℝ} (hs : Continuous strain)
    (hB : ∀ t, |strain t| ≤ B) {n₀ : ℕ} (hn₀ : regClock strain 10 < stationLevel n₀)
    (hres : ∀ n, n₀ ≤ n → |resid strain (station strain n) - resid strain (station strain n₀)| < 1) :
    OnePerGap (fun k => station strain (n₀ + k)) where
  mono := station_strictMono hs hB hn₀
  unbounded := station_tendsto hs hB hn₀
  one := by
    intro k
    have hlev : ∀ m, n₀ ≤ m → regClock strain 10 < stationLevel m :=
      fun m hm => lt_of_lt_of_le hn₀ (stationLevel_mono hm)
    have h1 := hres (n₀ + k) (by omega)
    have h2 := hres (n₀ + k + 1) (by omega)
    rw [resid_station hs hB (hlev _ (by omega)), resid_station hs hB (hlev _ le_rfl)] at h1 h2
    -- integer bookkeeping: N(t_m) − m is constant
    have e1 : ((stripZeroCountMult (station strain (n₀ + k)) : ℤ) - (n₀ + k : ℕ))
        = ((stripZeroCountMult (station strain n₀) : ℤ) - n₀) := by
      apply int_eq_of_abs_sub_lt_one
      push_cast
      convert h1 using 2
      push_cast
      ring
    have e2 : ((stripZeroCountMult (station strain (n₀ + k + 1)) : ℤ) - (n₀ + k + 1 : ℕ))
        = ((stripZeroCountMult (station strain n₀) : ℤ) - n₀) := by
      apply int_eq_of_abs_sub_lt_one
      push_cast
      convert h2 using 2
      push_cast
      ring
    have hband := bandCountMult_add (station_lt hs hB (hlev _ (by omega : n₀ ≤ n₀ + k))).le
    show bandCountMult (station strain (n₀ + k)) (station strain (n₀ + (k + 1))) = 1
    rw [show n₀ + (k + 1) = n₀ + k + 1 by omega]
    omega

/-- **RH from the residual law**, the first station at or below `58` (the compiled ladder covers the
range beneath). -/
theorem nontrivialZeros_online_of_resid {strain : ℝ → ℝ} {B : ℝ} (hs : Continuous strain)
    (hB : ∀ t, |strain t| ≤ B) {n₀ : ℕ} (hn₀ : regClock strain 10 < stationLevel n₀)
    (h58 : station strain n₀ ≤ 58)
    (hres : ∀ n, n₀ ≤ n → |resid strain (station strain n) - resid strain (station strain n₀)| < 1) :
    ∀ ρ ∈ ZD.NontrivialZeros, ρ.re = 1 / 2 :=
  nontrivialZeros_online_of_onePerGap_of_le_58 (onePerGap_of_resid hs hB hn₀ hres)
    (by simpa using h58)

/-- Every zero above the first station is simple as well. -/
theorem simple_of_resid {strain : ℝ → ℝ} {B : ℝ} (hs : Continuous strain)
    (hB : ∀ t, |strain t| ≤ B) {n₀ : ℕ} (hn₀ : regClock strain 10 < stationLevel n₀)
    (hres : ∀ n, n₀ ≤ n → |resid strain (station strain n) - resid strain (station strain n₀)| < 1)
    {ρ : ℂ} (hρ : ρ ∈ ZD.NontrivialZeros) (hpos : 0 < ρ.im) (hab : station strain n₀ < ρ.im) :
    ZD.xiOrderNat ρ = 1 :=
  (online_simple_of_onePerGap (onePerGap_of_resid hs hB hn₀ hres) hρ hpos (by simpa using hab)).2

end CriticalLinePhasor.ContourArgument

#print axioms CriticalLinePhasor.ContourArgument.station_spec
#print axioms CriticalLinePhasor.ContourArgument.resid_station
#print axioms CriticalLinePhasor.ContourArgument.onePerGap_of_resid
#print axioms CriticalLinePhasor.ContourArgument.nontrivialZeros_online_of_resid
