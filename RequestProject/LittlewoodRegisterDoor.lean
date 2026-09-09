import RequestProject.DVPLittlewoodTheorem
import RequestProject.DoubleCoshProgram
import RequestProject.DVPArgumentPrinciple

/-!
# The limit door: Littlewood's theorem turns the register identity into an average (ledger 677)

Littlewood's bound is compiled unconditionally (`littlewoodBound_holds`): `|∫₀ᵀ S_all| ≤ C(1 + log(1+T))` for the
full strip ledger `S_all = S_mult + N_off`.  One off-line zero at height `γ₀` makes `N_off ≥ 1` above `γ₀`, so
`∫₀ᵀ N_off ≥ T − γ₀` grows linearly, and then `∫₀ᵀ S_mult = ∫ S_all − ∫ N_off ≤ C(1 + log(1+T)) − (T − γ₀)` is
LINEARLY NEGATIVE.  Hence:

**`rh_of_smultIntegralSublinear`: if the on-line ledger's running integral is not linearly negative
(`∀ ε > 0, eventually −εT ≤ ∫₀ᵀ S_mult`), the Riemann Hypothesis holds.**

This is the register door in the limit: no census, no contour, no height range — only the fiber's own on-line
ledger `S_mult(t) = N_on(t) − 1 − ϑ(t)/π` (events on the carrier with multiplicity against the clock), asked to
keep pace with the clock ON AVERAGE.
-/

open Complex Filter Topology Set
open CriticalLinePhasor.CarrierScale CriticalLinePhasor.ContourArgument CriticalLinePhasor.ResidueJump
open DoubleCoshProgram

namespace CriticalLinePhasor.DVP

/-- **The on-line ledger keeps pace with the clock on average.** -/
def SmultIntegralSublinear : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ T in atTop, -(ε * T) ≤ ∫ t in (0:ℝ)..T, Smult t

/-- An off-line zero of height `γ₀ > 0` gives `N_off(T) ≥ 1` for every `T ≥ γ₀`. -/
theorem offLine_count_ge_one {ρ : ℂ} (hρ : ρ ∈ ZD.NontrivialZeros) (hoff : ρ.re ≠ 1 / 2)
    (hpos : 0 < ρ.im) {T : ℝ} (hT : ρ.im ≤ T) : 1 ≤ offLineStripZeroCountMult T := by
  have hmem : ρ ∈ stripZeroFinset T :=
    (stripZeroWindow_finite T).mem_toFinset.mpr ⟨hρ, hpos, hT⟩
  have h1 := xiOrderNat_le_offLineStripZeroCountMult_of_offCarrier hmem hoff
  have h2 : 1 ≤ ZD.xiOrderNat ρ := ZD.xiOrderNat_pos_of_mem_NontrivialZeros hρ
  omega

/-- The integrated off-line ledger grows at least linearly past an off-line zero. -/
theorem offline_integral_ge {γ₀ T : ℝ} (h0 : 0 ≤ γ₀) (hT : γ₀ ≤ T)
    (hN : ∀ t, γ₀ ≤ t → 1 ≤ offLineStripZeroCountMult t) :
    T - γ₀ ≤ ∫ t in (0:ℝ)..T, (offLineStripZeroCountMult t : ℝ) := by
  rw [← intervalIntegral.integral_add_adjacent_intervals (offline_intervalIntegrable 0 γ₀)
    (offline_intervalIntegrable γ₀ T)]
  have h1 : 0 ≤ ∫ t in (0:ℝ)..γ₀, (offLineStripZeroCountMult t : ℝ) :=
    intervalIntegral.integral_nonneg h0 (fun t _ => Nat.cast_nonneg _)
  have h2 : ∫ t in γ₀..T, (1 : ℝ) ≤ ∫ t in γ₀..T, (offLineStripZeroCountMult t : ℝ) :=
    intervalIntegral.integral_mono_on hT (by simp) (offline_intervalIntegrable γ₀ T)
      (fun t ht => by exact_mod_cast hN t ht.1)
  rw [intervalIntegral.integral_const, smul_eq_mul, mul_one] at h2
  linarith

/-- **The limit door.** -/
theorem noOffline_of_smultIntegralSublinear (h : SmultIntegralSublinear) : NoOfflineZeros := by
  intro ρ hρ
  by_contra hoff
  -- normalize to the upper half
  have him_ne : ρ.im ≠ 0 := by
    intro h0
    have hρre : ρ = ((ρ.re : ℝ) : ℂ) := by
      apply Complex.ext
      · simp
      · simpa using h0
    obtain ⟨ha, hb, hc⟩ := hρ
    rw [hρre] at hc
    exact zeta_ne_zero_of_real_unit ha hb hc
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
    fun t ht => offLine_count_ge_one hρ'_mem hρ'_re hρ'_im_pos ht
  obtain ⟨C, hC⟩ := littlewoodBound_holds
  -- log is eventually below a small multiple of the identity
  have hlog : ∀ᶠ T in atTop, Real.log (1 + T) ≤ 1 / (4 * (|C| + 1)) * (1 + T) := by
    have hsmall := Real.isLittleO_log_id_atTop.bound (c := 1 / (4 * (|C| + 1))) (by positivity)
    have hten : Tendsto (fun T : ℝ => 1 + T) atTop atTop := by
      simpa [add_comm] using (tendsto_id.atTop_add (tendsto_const_nhds (x := (1:ℝ))))
    filter_upwards [hten.eventually hsmall, eventually_ge_atTop (0:ℝ)] with T hT hT0
    have hpos : 0 ≤ Real.log (1 + T) := Real.log_nonneg (by linarith)
    simp only [id, Real.norm_eq_abs, abs_of_nonneg hpos, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 + T)] at hT
    exact hT
  have hε := h (1 / 2) (by norm_num)
  obtain ⟨T, hTε, hTlog, hTbig⟩ :=
    (hε.and (hlog.and (eventually_ge_atTop (max γ₀ (4 * (|C| + 1) + 4 * γ₀ + 4))))).exists
  have hTγ : γ₀ ≤ T := le_trans (le_max_left _ _) hTbig
  have hT0 : 0 ≤ T := le_trans hρ'_im_pos.le hTγ
  have hTbig' : 4 * (|C| + 1) + 4 * γ₀ + 4 ≤ T := le_trans (le_max_right _ _) hTbig
  have hsplit := integral_smult_split T
  have hLW := hC T hT0
  have hoffint := offline_integral_ge hρ'_im_pos.le hTγ hN
  have hlog0 : 0 ≤ Real.log (1 + T) := Real.log_nonneg (by linarith)
  have hAll : ∫ t in (0:ℝ)..T, SAll t ≤ |C| * (1 + Real.log (1 + T)) := by
    calc ∫ t in (0:ℝ)..T, SAll t ≤ |∫ t in (0:ℝ)..T, SAll t| := le_abs_self _
      _ ≤ C * (1 + Real.log (1 + T)) := hLW
      _ ≤ |C| * (1 + Real.log (1 + T)) := by gcongr; exact le_abs_self C
  have hCl : |C| * Real.log (1 + T) ≤ (1 + T) / 4 := by
    calc |C| * Real.log (1 + T) ≤ |C| * (1 / (4 * (|C| + 1)) * (1 + T)) := by gcongr
      _ = (|C| / (|C| + 1)) * ((1 + T) / 4) := by field_simp
      _ ≤ 1 * ((1 + T) / 4) := by
          gcongr
          rw [div_le_one (by positivity)]; linarith
      _ = (1 + T) / 4 := one_mul _
  -- assemble: −T/2 ≤ ∫Smult = ∫SAll − ∫N_off ≤ |C|(1 + log) − (T − γ₀) ≤ |C| + (1+T)/4 − T + γ₀
  have : -(1 / 2 * T) ≤ |C| + (1 + T) / 4 - T + γ₀ := by
    calc -(1 / 2 * T) ≤ ∫ t in (0:ℝ)..T, Smult t := hTε
      _ = (∫ t in (0:ℝ)..T, SAll t) - ∫ t in (0:ℝ)..T, (offLineStripZeroCountMult t : ℝ) := hsplit
      _ ≤ |C| * (1 + Real.log (1 + T)) - (T - γ₀) := by linarith
      _ ≤ |C| + (1 + T) / 4 - T + γ₀ := by nlinarith [abs_nonneg C]
  nlinarith [abs_nonneg C]

/-- **RH from the averaged register identity.** -/
theorem rh_of_smultIntegralSublinear (h : SmultIntegralSublinear) : RiemannHypothesis :=
  RiemannHypothesis_of_no_offline (noOffline_of_smultIntegralSublinear h)

end CriticalLinePhasor.DVP

#print axioms CriticalLinePhasor.DVP.rh_of_smultIntegralSublinear
