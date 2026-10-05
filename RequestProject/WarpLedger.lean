import RequestProject.LittlewoodRegisterDoor

/-!
# The warp ledger, built vanishing by vanishing (ledger 945)

Sam, 2026-09-30: "the warp is built vanishing by vanishing" — "ok, build it".

For vanishing heights `γ : ℕ → ℝ` with multiplicities `m : ℕ → ℕ` and a clock `θ`, the warp set at vanishing `N` is
`warp N = π·(m 0 + ⋯ + m N) − θ(γ N) − π/2`.

* `warp_succ` — from one vanishing to the next the warp gains `π·m(N+1)` (the vanishing) and loses the clock's
  advance across the gap.
* `warp_eq_sum` — so the warp is its first value plus the running sum of those gap increments.
* `smult_eq_warp` — when the on-line count at `γ N` is `m 0 + ⋯ + m N`, the registered ledger at the vanishing is
  `S_mult(γ N) = warp N / π − 1/2`.
* `noOffline_of_frequently_not_linearly_behind` — door 677 under a weaker hypothesis: it is enough that, for SOME
  `c < 1`, the ledger's running integral is above `−cT` at ARBITRARILY LARGE `T` (not every `ε`, not eventually).
-/

open Complex Filter Topology Set Finset
open CriticalLinePhasor.CarrierScale CriticalLinePhasor.ContourArgument CriticalLinePhasor.ResidueJump
open DoubleCoshProgram

namespace CriticalLinePhasor.WarpLedger

/-- The warp set at vanishing `N`. -/
noncomputable def warp (γ : ℕ → ℝ) (m : ℕ → ℕ) (θ : ℝ → ℝ) (N : ℕ) : ℝ :=
  Real.pi * (∑ n ∈ range (N + 1), (m n : ℝ)) - θ (γ N) - Real.pi / 2

/-- **One gap of the ledger**: the next vanishing adds `π·m(N+1)`; the clock's advance across the gap is subtracted. -/
theorem warp_succ (γ : ℕ → ℝ) (m : ℕ → ℕ) (θ : ℝ → ℝ) (N : ℕ) :
    warp γ m θ (N + 1) - warp γ m θ N = Real.pi * m (N + 1) - (θ (γ (N + 1)) - θ (γ N)) := by
  unfold warp
  rw [sum_range_succ _ (N + 1)]
  ring

/-- **The warp is built vanishing by vanishing**: its first value plus the running sum of the gap increments. -/
theorem warp_eq_sum (γ : ℕ → ℝ) (m : ℕ → ℕ) (θ : ℝ → ℝ) (N : ℕ) :
    warp γ m θ N = warp γ m θ 0
      + ∑ n ∈ range N, (Real.pi * m (n + 1) - (θ (γ (n + 1)) - θ (γ n))) := by
  induction N with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, ← add_assoc, ← ih]
    linarith [warp_succ γ m θ k]

/-- **The ledger at a vanishing is the registered ledger**: if the on-line count with multiplicity at `γ N` is
`m 0 + ⋯ + m N`, then `S_mult(γ N) = warp N / π − 1/2`. -/
theorem smult_eq_warp (γ : ℕ → ℝ) (m : ℕ → ℕ) (N : ℕ)
    (hcount : (zeroEventCountMult (γ N) : ℝ) = ∑ n ∈ range (N + 1), (m n : ℝ)) :
    Smult (γ N) = warp γ m theta N / Real.pi - 1 / 2 := by
  unfold Smult warp
  rw [hcount]
  field_simp
  ring

/-- **Door 677 under a weaker hypothesis.** If for some `c < 1` the running integral of the registered ledger is
above `−cT` at arbitrarily large heights `T`, no nontrivial zero is off the line. -/
theorem noOffline_of_frequently_not_linearly_behind
    (h : ∃ c : ℝ, c < 1 ∧ ∃ᶠ T in atTop, -(c * T) ≤ ∫ t in (0:ℝ)..T, Smult t) : NoOfflineZeros := by
  obtain ⟨c₀, hc₀1, hfreq₀⟩ := h
  -- replace c₀ by c = max c₀ 0, so that 0 ≤ c < 1
  set c : ℝ := max c₀ 0 with hcdef
  have hc1 : c < 1 := max_lt hc₀1 (by norm_num)
  have hc0 : 0 ≤ c := le_max_right _ _
  have hfreq : ∃ᶠ T in atTop, -(c * T) ≤ ∫ t in (0:ℝ)..T, Smult t :=
    (hfreq₀.and_eventually (eventually_ge_atTop (0:ℝ))).mono fun T hT =>
      le_trans (neg_le_neg (mul_le_mul_of_nonneg_right (le_max_left c₀ 0) hT.2)) hT.1
  intro ρ hρ
  by_contra hoff
  have him_ne : ρ.im ≠ 0 := by
    intro h0
    have hρre : ρ = ((ρ.re : ℝ) : ℂ) := by
      apply Complex.ext
      · simp
      · simpa using h0
    obtain ⟨ha, hb, hc⟩ := hρ
    rw [hρre] at hc
    exact CriticalLinePhasor.DVP.zeta_ne_zero_of_real_unit ha hb hc
  set ρ' : ℂ := if 0 < ρ.im then ρ else (starRingEnd ℂ) ρ with hρ'def
  have hρ'_mem : ρ' ∈ ZD.NontrivialZeros := by
    rw [hρ'def]
    split_ifs with hh
    · exact hρ
    · obtain ⟨ha, hb, hc⟩ := hρ
      refine ⟨by simpa using ha, by simpa using hb, ?_⟩
      rw [riemannZeta_conj, hc, map_zero]
  have hρ'_im_pos : 0 < ρ'.im := by
    rw [hρ'def]
    split_ifs with hh
    · exact hh
    · simp only [Complex.conj_im]
      rcases lt_trichotomy ρ.im 0 with h1 | h1 | h1
      · linarith
      · exact absurd h1 him_ne
      · exact absurd h1 hh
  have hρ'_re : ρ'.re ≠ 1 / 2 := by
    rw [hρ'def]
    split_ifs with hh
    · exact hoff
    · simpa using hoff
  set γ₀ := ρ'.im with hγ₀
  have hN : ∀ t, γ₀ ≤ t → 1 ≤ offLineStripZeroCountMult t :=
    fun t ht => CriticalLinePhasor.DVP.offLine_count_ge_one hρ'_mem hρ'_re hρ'_im_pos ht
  obtain ⟨C, hC⟩ := CriticalLinePhasor.DVP.littlewoodBound_holds
  set δ : ℝ := 1 - c with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  have hlog : ∀ᶠ T in atTop, Real.log (1 + T) ≤ δ / (4 * (|C| + 1)) * (1 + T) := by
    have hsmall := Real.isLittleO_log_id_atTop.bound (c := δ / (4 * (|C| + 1))) (by positivity)
    have hten : Tendsto (fun T : ℝ => 1 + T) atTop atTop := by
      simpa [add_comm] using (tendsto_id.atTop_add (tendsto_const_nhds (x := (1:ℝ))))
    filter_upwards [hten.eventually hsmall, eventually_ge_atTop (0:ℝ)] with T hT hT0
    have hpos : 0 ≤ Real.log (1 + T) := Real.log_nonneg (by linarith)
    simp only [id, Real.norm_eq_abs, abs_of_nonneg hpos, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 + T)] at hT
    exact hT
  obtain ⟨T, hTc, hTlog, hTbig⟩ :=
    (hfreq.and_eventually (hlog.and (eventually_ge_atTop
      (max γ₀ ((4 * (|C| + 1) + 4 * γ₀ + 4) / δ))))).exists
  have hTγ : γ₀ ≤ T := le_trans (le_max_left _ _) hTbig
  have hT0 : 0 ≤ T := le_trans hρ'_im_pos.le hTγ
  have hTbig' : (4 * (|C| + 1) + 4 * γ₀ + 4) / δ ≤ T := le_trans (le_max_right _ _) hTbig
  have hTbig'' : 4 * (|C| + 1) + 4 * γ₀ + 4 ≤ δ * T := by
    rw [div_le_iff₀ hδpos] at hTbig'; linarith
  have hsplit := CriticalLinePhasor.DVP.integral_smult_split T
  have hLW := hC T hT0
  have hoffint := CriticalLinePhasor.DVP.offline_integral_ge hρ'_im_pos.le hTγ hN
  have hAll : ∫ t in (0:ℝ)..T, CriticalLinePhasor.DVP.SAll t ≤ |C| * (1 + Real.log (1 + T)) := by
    calc ∫ t in (0:ℝ)..T, CriticalLinePhasor.DVP.SAll t
        ≤ |∫ t in (0:ℝ)..T, CriticalLinePhasor.DVP.SAll t| := le_abs_self _
      _ ≤ C * (1 + Real.log (1 + T)) := hLW
      _ ≤ |C| * (1 + Real.log (1 + T)) :=
          mul_le_mul_of_nonneg_right (le_abs_self C)
            (by have := Real.log_nonneg (show (1:ℝ) ≤ 1 + T by linarith); linarith)
  have hCl : |C| * Real.log (1 + T) ≤ δ * (1 + T) / 4 := by
    calc |C| * Real.log (1 + T) ≤ |C| * (δ / (4 * (|C| + 1)) * (1 + T)) := by gcongr
      _ = (|C| / (|C| + 1)) * (δ * (1 + T) / 4) := by field_simp
      _ ≤ 1 * (δ * (1 + T) / 4) := by
          gcongr
          rw [div_le_one (by positivity)]; linarith
      _ = δ * (1 + T) / 4 := one_mul _
  have key : -(c * T) ≤ |C| + δ * (1 + T) / 4 - T + γ₀ := by
    calc -(c * T) ≤ ∫ t in (0:ℝ)..T, Smult t := hTc
      _ = (∫ t in (0:ℝ)..T, CriticalLinePhasor.DVP.SAll t)
            - ∫ t in (0:ℝ)..T, (offLineStripZeroCountMult t : ℝ) := hsplit
      _ ≤ |C| * (1 + Real.log (1 + T)) - (T - γ₀) := by linarith
      _ ≤ |C| + δ * (1 + T) / 4 - T + γ₀ := by nlinarith [abs_nonneg C]
  have hδle : δ ≤ 1 := by rw [hδ]; linarith
  have hcT : c * T = T - δ * T := by rw [hδ]; ring
  have hδT : δ * (1 + T) / 4 = δ / 4 + δ * T / 4 := by ring
  rw [hcT, hδT] at key
  linarith [abs_nonneg C, hρ'_im_pos]

end CriticalLinePhasor.WarpLedger

#print axioms CriticalLinePhasor.WarpLedger.warp_eq_sum
#print axioms CriticalLinePhasor.WarpLedger.smult_eq_warp
#print axioms CriticalLinePhasor.WarpLedger.noOffline_of_frequently_not_linearly_behind
