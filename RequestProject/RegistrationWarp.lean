import RequestProject.RegistrationMaster

/-!
# The height-matched bank: stations of a warped clock (ledger 611)

The registry's bank grows with height (`L ≈ 0.8 log t`): the Riesz scale is a function of the
height, a warp, not a constant. Here:

1. Stations exist for ANY continuous strain whose clock tends to infinity (the bounded-strain
   hypothesis of 601 is replaced by `Tendsto (regClock strain) atTop atTop`); the residual law
   still gives one zero per gap and RH (`nontrivialZeros_online_of_resid'`).
2. `warpStrain Lf t := rieszStrain (Lf t) t` is continuous for continuous positive `Lf`
   (`rieszStrain` is jointly continuous in `(L, t)`: off the cutoff the profile vanishes, so locally
   the sum runs over a fixed range), and its clock tends to infinity as soon as
   `exp (Lf t) ≤ t/20` eventually (the crude bound `|Ŝ_L| ≤ (e^L + 1)/π`).
3. **`warp_gap_count`**: over a station gap `(a, b]` of the warped clock, with `L_a = Lf a`,

     `N(a, b] = 1 + (1/π)∫_a^b rem_{L_a} + boundaryTerm L_a a b − (Ŝ_{Lf b}(b) − Ŝ_{L_a}(b))`.

   The last term is the bank change across the gap, exact, and it is small: for `L ≤ L'`,
   `|Ŝ_{L'}(t) − Ŝ_L(t)| ≤ (1/π)((L' − L)/L)(e^{L'} + 1)` (`abs_rieszStrain_sub_le`), since the
   Riesz profile moves by at most `(L' − L)/L` when the scale moves from `L` to `L'`.
-/

open Complex Set MeasureTheory Filter Topology
open scoped Interval Real
open CriticalLinePhasor.CarrierScale (theta clockRate continuous_clockRate)

namespace CriticalLinePhasor.ContourArgument

/-! ## 1. Stations of any clock tending to infinity -/

theorem station_exists' {strain : ℝ → ℝ} (hs : Continuous strain)
    (hT : Tendsto (regClock strain) atTop atTop)
    {n : ℕ} (hn : regClock strain 10 < stationLevel n) :
    ∃ t, 10 ≤ t ∧ regClock strain t = stationLevel n := by
  obtain ⟨T, hT⟩ := (tendsto_atTop_atTop.1 hT) (stationLevel n)
  have hb : stationLevel n ≤ regClock strain (max 10 T) := hT _ (le_max_right _ _)
  have hmem : stationLevel n ∈ Icc (regClock strain 10) (regClock strain (max 10 T)) := ⟨hn.le, hb⟩
  obtain ⟨t, ht, hGt⟩ := intermediate_value_Icc (le_max_left (10:ℝ) T)
    (regClock_continuous hs).continuousOn hmem
  exact ⟨t, ht.1, hGt⟩

theorem station_spec' {strain : ℝ → ℝ} (hs : Continuous strain)
    (hT : Tendsto (regClock strain) atTop atTop)
    {n : ℕ} (hn : regClock strain 10 < stationLevel n) :
    10 ≤ station strain n ∧ regClock strain (station strain n) = stationLevel n :=
  (station_set_closed hs n).csInf_mem (station_exists' hs hT hn) (station_set_bddBelow strain n)

theorem station_lt' {strain : ℝ → ℝ} (hs : Continuous strain)
    (hT : Tendsto (regClock strain) atTop atTop)
    {n : ℕ} (hn : regClock strain 10 < stationLevel n) :
    station strain n < station strain (n + 1) := by
  have hn' : regClock strain 10 < stationLevel (n + 1) := by
    rw [stationLevel_succ]; linarith
  obtain ⟨h1, hG1⟩ := station_spec' hs hT hn
  obtain ⟨h2, hG2⟩ := station_spec' hs hT hn'
  by_contra hle
  simp only [not_lt] at hle
  have hmem : stationLevel n ∈ Icc (regClock strain 10) (regClock strain (station strain (n + 1))) :=
    ⟨hn.le, by rw [hG2, stationLevel_succ]; linarith⟩
  obtain ⟨s, hs', hGs⟩ := intermediate_value_Icc h2 (regClock_continuous hs).continuousOn hmem
  have hle' : station strain n ≤ s := csInf_le (station_set_bddBelow strain n) ⟨hs'.1, hGs⟩
  have heq : station strain n = station strain (n + 1) := le_antisymm (hle'.trans hs'.2) hle
  rw [heq, hG2, stationLevel_succ] at hG1
  linarith

theorem station_strictMono' {strain : ℝ → ℝ} (hs : Continuous strain)
    (hT : Tendsto (regClock strain) atTop atTop)
    {n₀ : ℕ} (hn₀ : regClock strain 10 < stationLevel n₀) :
    StrictMono (fun k => station strain (n₀ + k)) := by
  apply strictMono_nat_of_lt_succ
  intro k
  have : regClock strain 10 < stationLevel (n₀ + k) :=
    lt_of_lt_of_le hn₀ (stationLevel_mono (by omega))
  show station strain (n₀ + k) < station strain (n₀ + (k + 1))
  rw [show n₀ + (k + 1) = n₀ + k + 1 by omega]
  exact station_lt' hs hT this

theorem station_tendsto' {strain : ℝ → ℝ} (hs : Continuous strain)
    (hT : Tendsto (regClock strain) atTop atTop)
    {n₀ : ℕ} (hn₀ : regClock strain 10 < stationLevel n₀) :
    Tendsto (fun k => station strain (n₀ + k)) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro M
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := (10:ℝ)) (b := max 10 M)).exists_bound_of_continuousOn
    (regClock_continuous hs).continuousOn
  refine ⟨⌈K⌉₊ + 2, fun k hk => ?_⟩
  have hn : regClock strain 10 < stationLevel (n₀ + k) :=
    lt_of_lt_of_le hn₀ (stationLevel_mono (by omega))
  obtain ⟨h10, hG⟩ := station_spec' hs hT hn
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

theorem resid_station' {strain : ℝ → ℝ} (hs : Continuous strain)
    (hT : Tendsto (regClock strain) atTop atTop)
    {n : ℕ} (hn : regClock strain 10 < stationLevel n) :
    resid strain (station strain n) = (stripZeroCountMult (station strain n) : ℝ) - n + 1 / 2 := by
  have h := (station_spec' hs hT hn).2
  unfold regClock stationLevel at h
  unfold resid
  linarith

/-- The residual law gives one zero per gap, for any clock tending to infinity. -/
theorem onePerGap_of_resid' {strain : ℝ → ℝ} (hs : Continuous strain)
    (hT : Tendsto (regClock strain) atTop atTop)
    {n₀ : ℕ} (hn₀ : regClock strain 10 < stationLevel n₀)
    (hres : ∀ n, n₀ ≤ n → |resid strain (station strain n) - resid strain (station strain n₀)| < 1) :
    OnePerGap (fun k => station strain (n₀ + k)) where
  mono := station_strictMono' hs hT hn₀
  unbounded := station_tendsto' hs hT hn₀
  one := by
    intro k
    have hlev : ∀ m, n₀ ≤ m → regClock strain 10 < stationLevel m :=
      fun m hm => lt_of_lt_of_le hn₀ (stationLevel_mono hm)
    have h1 := hres (n₀ + k) (by omega)
    have h2 := hres (n₀ + k + 1) (by omega)
    rw [resid_station' hs hT (hlev _ (by omega)), resid_station' hs hT (hlev _ le_rfl)] at h1 h2
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
    have hband := bandCountMult_add (station_lt' hs hT (hlev _ (by omega : n₀ ≤ n₀ + k))).le
    show bandCountMult (station strain (n₀ + k)) (station strain (n₀ + (k + 1))) = 1
    rw [show n₀ + (k + 1) = n₀ + k + 1 by omega]
    omega

/-- RH from the residual law of any clock tending to infinity, first station at or below `58`. -/
theorem nontrivialZeros_online_of_resid' {strain : ℝ → ℝ} (hs : Continuous strain)
    (hT : Tendsto (regClock strain) atTop atTop)
    {n₀ : ℕ} (hn₀ : regClock strain 10 < stationLevel n₀)
    (h58 : station strain n₀ ≤ 58)
    (hres : ∀ n, n₀ ≤ n → |resid strain (station strain n) - resid strain (station strain n₀)| < 1) :
    ∀ ρ ∈ ZD.NontrivialZeros, ρ.re = 1 / 2 :=
  nontrivialZeros_online_of_onePerGap_of_le_58 (onePerGap_of_resid' hs hT hn₀ hres)
    (by simpa using h58)

/-! ## 2. The Riesz strain as a function of the scale -/

/-- Off the cutoff the profile vanishes: the strain is a sum over any range containing the cutoff. -/
theorem rieszStrain_eq_sum_range {L : ℝ} (hL : 0 < L) {M : ℕ} (hM : ⌊Real.exp L⌋₊ ≤ M) (t : ℝ) :
    rieszStrain L t
      = -(1 / Real.pi) * ∑ n ∈ Finset.range (M + 1), rieszProfile L (Real.log n) * strainClock n t := by
  unfold rieszStrain
  congr 1
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro n hn hn'
  rw [Finset.mem_range, not_lt] at hn'
  have hlt : Real.exp L < n := by
    have h1 : Real.exp L < (⌊Real.exp L⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    have h2 : ((⌊Real.exp L⌋₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn'
    push_cast at h2
    linarith
  have hlog : L ≤ Real.log n := by
    rw [← Real.log_exp L]
    exact Real.log_le_log (Real.exp_pos L) hlt.le
  rw [rieszProfile_eq_zero_of_ge hL hlog, zero_mul]

/-- The profile is jointly continuous in `(L, v)` at positive scale. -/
theorem rieszProfile_continuousAt_pair {L₀ : ℝ} (hL₀ : 0 < L₀) (v : ℝ) (t₀ : ℝ) :
    ContinuousAt (fun p : ℝ × ℝ => rieszProfile p.1 v) (L₀, t₀) := by
  unfold rieszProfile rampR1
  apply ContinuousAt.div
  · exact (by fun_prop : Continuous (fun p : ℝ × ℝ => max (p.1 - v) 0 - max (0 - v) 0)).continuousAt
  · exact continuousAt_fst
  · exact hL₀.ne'

/-- **The Riesz strain is jointly continuous in `(L, t)` at positive scale.** -/
theorem rieszStrain_continuousAt {L₀ t₀ : ℝ} (hL₀ : 0 < L₀) :
    ContinuousAt (fun p : ℝ × ℝ => rieszStrain p.1 p.2) (L₀, t₀) := by
  set M := ⌊Real.exp (L₀ + 1)⌋₊ with hM
  have hnhds : {p : ℝ × ℝ | 0 < p.1 ∧ p.1 < L₀ + 1} ∈ 𝓝 (L₀, t₀) := by
    apply IsOpen.mem_nhds
    · exact (isOpen_lt continuous_const continuous_fst).inter (isOpen_lt continuous_fst continuous_const)
    · exact ⟨hL₀, by linarith⟩
  have heq : ∀ p ∈ {p : ℝ × ℝ | 0 < p.1 ∧ p.1 < L₀ + 1},
      -(1 / Real.pi) * ∑ n ∈ Finset.range (M + 1), rieszProfile p.1 (Real.log n) * strainClock n p.2
        = rieszStrain p.1 p.2 := by
    intro p hp
    rw [rieszStrain_eq_sum_range hp.1 (M := M) (Nat.floor_mono (Real.exp_le_exp.2 hp.2.le))]
  have hcont : ContinuousAt (fun p : ℝ × ℝ =>
      -(1 / Real.pi) * ∑ n ∈ Finset.range (M + 1), rieszProfile p.1 (Real.log n) * strainClock n p.2)
      (L₀, t₀) := by
    apply ContinuousAt.mul continuousAt_const
    have hterm : ∀ n : ℕ, ContinuousAt
        (fun p : ℝ × ℝ => rieszProfile p.1 (Real.log n) * strainClock n p.2) (L₀, t₀) :=
      fun n => (rieszProfile_continuousAt_pair hL₀ (Real.log n) t₀).mul
        ((strainClock_continuous n).comp continuous_snd).continuousAt
    unfold ContinuousAt
    exact tendsto_finsetSum _ (fun n _ => (hterm n).tendsto)
  exact hcont.congr (eventually_of_mem hnhds heq)

/-- The height-matched strain: the Riesz strain at scale `Lf t`. -/
noncomputable def warpStrain (Lf : ℝ → ℝ) (t : ℝ) : ℝ := rieszStrain (Lf t) t

theorem warpStrain_continuous {Lf : ℝ → ℝ} (hLc : Continuous Lf) (hLpos : ∀ t, 0 < Lf t) :
    Continuous (warpStrain Lf) := by
  rw [continuous_iff_continuousAt]
  intro t
  have h := rieszStrain_continuousAt (t₀ := t) (hLpos t)
  have hg : ContinuousAt (fun x : ℝ => (Lf x, x)) t := (hLc.prodMk continuous_id).continuousAt
  exact ContinuousAt.comp (g := fun p : ℝ × ℝ => rieszStrain p.1 p.2) (f := fun x : ℝ => (Lf x, x)) h hg

/-! ## 3. Growth of the strain and of the warped clock -/

theorem abs_strainAmp_le_one (n : ℕ) : |strainAmp n| ≤ 1 := by
  unfold strainAmp
  by_cases hn : n ≤ 1
  · interval_cases n <;> simp [ArithmeticFunction.vonMangoldt_apply]
  · rw [not_le] at hn
    have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
    have hsqrt : 1 ≤ Real.sqrt n := Real.one_le_sqrt.2 (by exact_mod_cast (by omega : 1 ≤ n))
    rw [abs_of_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)),
      div_le_one (by positivity)]
    calc ArithmeticFunction.vonMangoldt n ≤ Real.log n := ArithmeticFunction.vonMangoldt_le_log
      _ = 1 * Real.log n := by ring
      _ ≤ Real.sqrt n * Real.log n := mul_le_mul_of_nonneg_right hsqrt hlog.le

theorem abs_rieszProfile_le_one {L : ℝ} (hL : 0 < L) {v : ℝ} (hv : 0 ≤ v) :
    |rieszProfile L v| ≤ 1 := by
  rw [rieszProfile_eq hL hv, abs_of_nonneg (le_max_right _ _)]
  apply max_le _ zero_le_one
  have : 0 ≤ v / L := by positivity
  linarith

/-- The crude growth bound `|Ŝ_L(t)| ≤ (e^L + 1)/π`. -/
theorem abs_rieszStrain_le' {L : ℝ} (hL : 0 < L) (t : ℝ) :
    |rieszStrain L t| ≤ (1 / Real.pi) * (Real.exp L + 1) := by
  refine (abs_rieszStrain_le L t).trans ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc ∑ n ∈ Finset.range (⌊Real.exp L⌋₊ + 1), |rieszProfile L (Real.log n)| * |strainAmp n|
      ≤ ∑ n ∈ Finset.range (⌊Real.exp L⌋₊ + 1), (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro n _
        calc |rieszProfile L (Real.log n)| * |strainAmp n| ≤ 1 * 1 :=
              mul_le_mul (abs_rieszProfile_le_one hL (Real.log_natCast_nonneg n))
                (abs_strainAmp_le_one n) (abs_nonneg _) zero_le_one
          _ = 1 := by ring
    _ = ((⌊Real.exp L⌋₊ + 1 : ℕ) : ℝ) := by simp
    _ ≤ Real.exp L + 1 := by
        push_cast
        linarith [Nat.floor_le (Real.exp_pos L).le]

/-- The warped clock tends to infinity as soon as `e^{Lf t} ≤ t/20` eventually. -/
theorem warp_regClock_tendsto {Lf : ℝ → ℝ} (hLpos : ∀ t, 0 < Lf t) {T₀ : ℝ}
    (hgrow : ∀ t, T₀ ≤ t → Real.exp (Lf t) ≤ t / 20) :
    Tendsto (regClock (warpStrain Lf)) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro M
  have hπ := Real.pi_pos
  refine ⟨max (max 10 T₀) (20 * (Real.pi * M - theta 10 + 2)), fun t ht => ?_⟩
  have ht10 : 10 ≤ t := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) ht)
  have htT : T₀ ≤ t := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) ht)
  have ht2 : 20 * (Real.pi * M - theta 10 + 2) ≤ t := le_trans (le_max_right _ _) ht
  have hg := theta_growth ht10
  have hs := abs_rieszStrain_le' (hLpos t) t
  have hexp := hgrow t htT
  have hlow : -((1 / Real.pi) * (t / 20 + 1)) ≤ warpStrain Lf t := by
    unfold warpStrain
    have h1 := (abs_le.1 hs).1
    have h2 : (1 / Real.pi) * (Real.exp (Lf t) + 1) ≤ (1 / Real.pi) * (t / 20 + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  unfold regClock
  have hθ : Real.pi * M + t / 20 + 1 ≤ theta t := by nlinarith
  have : M + (1 / Real.pi) * (t / 20 + 1) ≤ theta t / Real.pi := by
    rw [le_div_iff₀ hπ]
    have : (M + (1 / Real.pi) * (t / 20 + 1)) * Real.pi = Real.pi * M + (t / 20 + 1) := by
      field_simp
    rw [this]
    linarith
  linarith

/-! ## 4. The gap count of the warped clock -/

/-- **The count over a station gap of the warped clock**: one, plus the remainder, plus the boundary
term at the scale of the lower station, minus the bank change across the gap. -/
theorem warp_gap_count {Lf : ℝ → ℝ} (hLc : Continuous Lf) (hLpos : ∀ t, 0 < Lf t)
    (hT : Tendsto (regClock (warpStrain Lf)) atTop atTop)
    {n : ℕ} (hn : regClock (warpStrain Lf) 10 < stationLevel n) :
    (bandCountMult (station (warpStrain Lf) n) (station (warpStrain Lf) (n + 1)) : ℝ)
      = 1 + (1 / Real.pi) * (∫ t in station (warpStrain Lf) n..station (warpStrain Lf) (n + 1),
              rieszRemainder (Lf (station (warpStrain Lf) n)) t)
        + boundaryTerm (Lf (station (warpStrain Lf) n)) (station (warpStrain Lf) n)
            (station (warpStrain Lf) (n + 1))
        - (rieszStrain (Lf (station (warpStrain Lf) (n + 1))) (station (warpStrain Lf) (n + 1))
            - rieszStrain (Lf (station (warpStrain Lf) n)) (station (warpStrain Lf) (n + 1))) := by
  set a := station (warpStrain Lf) n with ha
  set b := station (warpStrain Lf) (n + 1) with hb
  have hs := warpStrain_continuous hLc hLpos
  have hn' : regClock (warpStrain Lf) 10 < stationLevel (n + 1) := by
    rw [stationLevel_succ]; linarith
  obtain ⟨ha10, hGa⟩ := station_spec' hs hT hn
  obtain ⟨hb10, hGb⟩ := station_spec' hs hT hn'
  have hab : a ≤ b := (station_lt' hs hT hn).le
  have hid := count_identity (hLpos a) (by linarith : (0:ℝ) < a) hab
  have hGa' : theta a / Real.pi + rieszStrain (Lf a) a = stationLevel n := hGa
  have hGb' : theta b / Real.pi + rieszStrain (Lf b) b = stationLevel n + 1 := by
    rw [← stationLevel_succ]; exact hGb
  rw [hid]
  have : (theta b - theta a) / Real.pi = theta b / Real.pi - theta a / Real.pi := by ring
  linarith

/-! ## 5. The bank change is small -/

/-- Moving the scale from `L` to `L' ≥ L` moves the profile by at most `(L' − L)/L`, upward. -/
theorem rieszProfile_sub_bounds {L L' v : ℝ} (hL : 0 < L) (hLL' : L ≤ L') (hv : 0 ≤ v) :
    0 ≤ rieszProfile L' v - rieszProfile L v ∧ rieszProfile L' v - rieszProfile L v ≤ (L' - L) / L := by
  have hL' : 0 < L' := by linarith
  rw [rieszProfile_eq hL' hv, rieszProfile_eq hL hv]
  have hdiv : v / L' ≤ v / L := div_le_div_of_nonneg_left hv hL hLL'
  constructor
  · rw [sub_nonneg]
    exact max_le_max (by linarith) le_rfl
  · rcases le_or_gt v L' with hvL' | hvL'
    · -- `v ≤ L'`: the Lipschitz bound on `max`, and `v/L − v/L' = v(L'−L)/(LL') ≤ (L'−L)/L`
      have h1 := abs_max_sub_max_le_abs (1 - v / L') (1 - v / L) 0
      have h2 : |(1 - v / L') - (1 - v / L)| = v / L - v / L' := by
        rw [abs_of_nonneg (by linarith)]; ring
      have h3 : v / L - v / L' ≤ (L' - L) / L := by
        rw [div_sub_div _ _ hL.ne' hL'.ne', div_le_div_iff₀ (by positivity) hL]
        nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 hLL') hL.le) (sub_nonneg.2 hvL')]
      have h4 := le_abs_self (max (1 - v / L') 0 - max (1 - v / L) 0)
      linarith
    · -- `v > L'`: both profiles vanish
      have e1 : max (1 - v / L') 0 = 0 := max_eq_right (by rw [sub_nonpos, one_le_div hL']; linarith)
      have e2 : max (1 - v / L) 0 = 0 := max_eq_right (by rw [sub_nonpos, one_le_div hL]; linarith)
      rw [e1, e2, sub_zero]
      positivity

/-- **The bank change across scales**: `|Ŝ_{L'}(t) − Ŝ_L(t)| ≤ (1/π)((L' − L)/L)(e^{L'} + 1)`. -/
theorem abs_rieszStrain_sub_le {L L' : ℝ} (hL : 0 < L) (hLL' : L ≤ L') (t : ℝ) :
    |rieszStrain L' t - rieszStrain L t| ≤ (1 / Real.pi) * ((L' - L) / L) * (Real.exp L' + 1) := by
  have hL' : 0 < L' := by linarith
  set M := ⌊Real.exp L'⌋₊ with hM
  have hδ : 0 ≤ (L' - L) / L := by positivity
  rw [rieszStrain_eq_sum_range hL (M := M) (Nat.floor_mono (Real.exp_le_exp.2 hLL')) t,
    rieszStrain_eq_sum_range hL' (M := M) le_rfl t, ← mul_sub, ← Finset.sum_sub_distrib, abs_mul,
    abs_neg, abs_of_pos (by positivity : (0:ℝ) < 1 / Real.pi)]
  calc (1 / Real.pi) * |∑ n ∈ Finset.range (M + 1),
        (rieszProfile L' (Real.log n) * strainClock n t - rieszProfile L (Real.log n) * strainClock n t)|
      ≤ (1 / Real.pi) * ∑ n ∈ Finset.range (M + 1), (L' - L) / L := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun n _ => ?_))
        rw [← sub_mul, abs_mul]
        obtain ⟨h0, h1⟩ := rieszProfile_sub_bounds hL hLL' (Real.log_natCast_nonneg n)
        calc |rieszProfile L' (Real.log n) - rieszProfile L (Real.log n)| * |strainClock n t|
            ≤ ((L' - L) / L) * 1 := by
              apply mul_le_mul _ ((abs_strainClock_le n t).trans (abs_strainAmp_le_one n))
                (abs_nonneg _) hδ
              rw [abs_of_nonneg h0]; exact h1
          _ = (L' - L) / L := mul_one _
    _ = (1 / Real.pi) * (((M + 1 : ℕ) : ℝ) * ((L' - L) / L)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ (1 / Real.pi) * ((L' - L) / L) * (Real.exp L' + 1) := by
        have hM1 : ((M + 1 : ℕ) : ℝ) ≤ Real.exp L' + 1 := by
          push_cast
          linarith [Nat.floor_le (Real.exp_pos L').le]
        rw [mul_assoc]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_left hM1 hδ

end CriticalLinePhasor.ContourArgument

#print axioms CriticalLinePhasor.ContourArgument.nontrivialZeros_online_of_resid'
#print axioms CriticalLinePhasor.ContourArgument.rieszStrain_continuousAt
#print axioms CriticalLinePhasor.ContourArgument.warp_regClock_tendsto
#print axioms CriticalLinePhasor.ContourArgument.warp_gap_count
#print axioms CriticalLinePhasor.ContourArgument.abs_rieszStrain_sub_le
