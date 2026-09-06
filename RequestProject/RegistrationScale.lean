import RequestProject.RegistrationWarp

/-!
# The registry's scale `c · log t` and the concrete stations (ledger 612)

`logScale c t = c · log (max t 2)`: continuous, positive for `c > 0`, with `exp (logScale c t) = t^c`
at heights `≥ 2`. For `0 < c < 1` the growth condition of `warp_regClock_tendsto` holds beyond the
explicit threshold `20^{1/(1−c)}`, so the warped clock has stations, and every theorem of
`RegistrationWarp.lean` instantiates: `registry_gap_count` (the exact gap count with the bank
change), `registry_bankChange_le` (the bank change bounded by `(1/π)(log(b/a)/log a)(b^c + 1)`),
and the door `nontrivialZeros_online_of_registryResid`. This is the registry of HP_PROGRAM §1 in
Lean: primes up to `t^c`, Riesz-tapered, stations at the half-integer levels of `ϑ/π + Ŝ`.
-/

open Complex Set MeasureTheory Filter Topology
open scoped Interval Real
open CriticalLinePhasor.CarrierScale (theta clockRate continuous_clockRate)

namespace CriticalLinePhasor.ContourArgument

/-- The registry's scale: `c · log t`, floored at height `2`. -/
noncomputable def logScale (c : ℝ) (t : ℝ) : ℝ := c * Real.log (max t 2)

theorem logScale_continuous (c : ℝ) : Continuous (logScale c) := by
  unfold logScale
  apply continuous_const.mul
  apply Continuous.log (continuous_id.max continuous_const)
  intro t
  exact (lt_of_lt_of_le two_pos (le_max_right t 2)).ne'

theorem logScale_pos {c : ℝ} (hc : 0 < c) (t : ℝ) : 0 < logScale c t := by
  unfold logScale
  apply mul_pos hc
  apply Real.log_pos
  exact lt_of_lt_of_le one_lt_two (le_max_right t 2)

theorem exp_logScale (c t : ℝ) : Real.exp (logScale c t) = (max t 2) ^ c := by
  unfold logScale
  rw [Real.rpow_def_of_pos (lt_of_lt_of_le two_pos (le_max_right t 2))]
  ring_nf

theorem logScale_mono {c : ℝ} (hc : 0 < c) {a b : ℝ} (hab : a ≤ b) : logScale c a ≤ logScale c b := by
  unfold logScale
  apply mul_le_mul_of_nonneg_left _ hc.le
  apply Real.log_le_log (lt_of_lt_of_le two_pos (le_max_right a 2))
  exact max_le_max hab le_rfl

/-- For `0 < c < 1`, `t^c ≤ t/20` beyond the explicit threshold `20^{1/(1−c)}`. -/
theorem logScale_growth {c : ℝ} (hc : 0 < c) (hc1 : c < 1) :
    ∀ t, max ((20:ℝ) ^ (1 / (1 - c))) 2 ≤ t → Real.exp (logScale c t) ≤ t / 20 := by
  intro t ht
  have ht2 : (2:ℝ) ≤ t := le_trans (le_max_right _ _) ht
  have htT : (20:ℝ) ^ (1 / (1 - c)) ≤ t := le_trans (le_max_left _ _) ht
  have htpos : 0 < t := by linarith
  rw [exp_logScale, max_eq_left ht2]
  have h1c : 0 < 1 - c := by linarith
  have hpow : (20:ℝ) ≤ t ^ (1 - c) := by
    calc (20:ℝ) = ((20:ℝ) ^ (1 / (1 - c))) ^ (1 - c) := by
          rw [← Real.rpow_mul (by norm_num), div_mul_cancel₀ _ h1c.ne', Real.rpow_one]
      _ ≤ t ^ (1 - c) := Real.rpow_le_rpow (by positivity) htT h1c.le
  have hsplit : t ^ c * t ^ (1 - c) = t := by
    rw [← Real.rpow_add htpos, show c + (1 - c) = (1:ℝ) by ring, Real.rpow_one]
  rw [le_div_iff₀ (by norm_num : (0:ℝ) < 20)]
  calc t ^ c * 20 ≤ t ^ c * t ^ (1 - c) := mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = t := hsplit

/-! ## The registry -/

/-- The registry's strain: the Riesz strain at scale `c · log t`. -/
noncomputable def registryStrain (c : ℝ) : ℝ → ℝ := warpStrain (logScale c)

theorem registryStrain_continuous {c : ℝ} (hc : 0 < c) : Continuous (registryStrain c) :=
  warpStrain_continuous (logScale_continuous c) (logScale_pos hc)

theorem registry_regClock_tendsto {c : ℝ} (hc : 0 < c) (hc1 : c < 1) :
    Tendsto (regClock (registryStrain c)) atTop atTop :=
  warp_regClock_tendsto (logScale_pos hc) (logScale_growth hc hc1)

/-- The registry's stations. -/
noncomputable def registryStation (c : ℝ) (n : ℕ) : ℝ := station (registryStrain c) n

theorem registryStation_spec {c : ℝ} (hc : 0 < c) (hc1 : c < 1) {n : ℕ}
    (hn : regClock (registryStrain c) 10 < stationLevel n) :
    10 ≤ registryStation c n ∧ regClock (registryStrain c) (registryStation c n) = stationLevel n :=
  station_spec' (registryStrain_continuous hc) (registry_regClock_tendsto hc hc1) hn

theorem registryStation_lt {c : ℝ} (hc : 0 < c) (hc1 : c < 1) {n : ℕ}
    (hn : regClock (registryStrain c) 10 < stationLevel n) :
    registryStation c n < registryStation c (n + 1) :=
  station_lt' (registryStrain_continuous hc) (registry_regClock_tendsto hc hc1) hn

/-- **The registry's gap count**, exact: one, plus the remainder and the boundary term at the lower
station's scale, minus the bank change. -/
theorem registry_gap_count {c : ℝ} (hc : 0 < c) (hc1 : c < 1) {n : ℕ}
    (hn : regClock (registryStrain c) 10 < stationLevel n) :
    (bandCountMult (registryStation c n) (registryStation c (n + 1)) : ℝ)
      = 1 + (1 / Real.pi) * (∫ t in registryStation c n..registryStation c (n + 1),
              rieszRemainder (logScale c (registryStation c n)) t)
        + boundaryTerm (logScale c (registryStation c n)) (registryStation c n)
            (registryStation c (n + 1))
        - (rieszStrain (logScale c (registryStation c (n + 1))) (registryStation c (n + 1))
            - rieszStrain (logScale c (registryStation c n)) (registryStation c (n + 1))) :=
  warp_gap_count (logScale_continuous c) (logScale_pos hc) (registry_regClock_tendsto hc hc1) hn

/-- **The bank change across a registry gap** is at most `(1/π)(log(b/a)/log a)(b^c + 1)`. -/
theorem registry_bankChange_le {c : ℝ} (hc : 0 < c) {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) (t : ℝ) :
    |rieszStrain (logScale c b) t - rieszStrain (logScale c a) t|
      ≤ (1 / Real.pi) * ((Real.log b - Real.log a) / Real.log a) * (b ^ c + 1) := by
  have h := abs_rieszStrain_sub_le (logScale_pos hc a) (logScale_mono hc hab) t
  have hb2 : (2:ℝ) ≤ b := ha.trans hab
  have hloga : 0 < Real.log a := Real.log_pos (by linarith)
  rw [exp_logScale, max_eq_left hb2] at h
  refine h.trans (le_of_eq ?_)
  unfold logScale
  rw [max_eq_left ha, max_eq_left hb2]
  congr 2
  field_simp

/-- **RH from the registry's residual law.** -/
theorem nontrivialZeros_online_of_registryResid {c : ℝ} (hc : 0 < c) (hc1 : c < 1) {n₀ : ℕ}
    (hn₀ : regClock (registryStrain c) 10 < stationLevel n₀)
    (h58 : registryStation c n₀ ≤ 58)
    (hres : ∀ n, n₀ ≤ n →
      |resid (registryStrain c) (registryStation c n) - resid (registryStrain c) (registryStation c n₀)| < 1) :
    ∀ ρ ∈ ZD.NontrivialZeros, ρ.re = 1 / 2 :=
  nontrivialZeros_online_of_resid' (registryStrain_continuous hc) (registry_regClock_tendsto hc hc1)
    hn₀ h58 hres

end CriticalLinePhasor.ContourArgument

#print axioms CriticalLinePhasor.ContourArgument.logScale_growth
#print axioms CriticalLinePhasor.ContourArgument.registry_gap_count
#print axioms CriticalLinePhasor.ContourArgument.registry_bankChange_le
#print axioms CriticalLinePhasor.ContourArgument.nontrivialZeros_online_of_registryResid
