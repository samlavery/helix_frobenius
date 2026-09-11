import RequestProject.RegistrationPrimeMean
import RequestProject.LittlewoodRegisterDoor
import RequestProject.RHSourceStatement

/-!
# Bounding the residual: primes fuel S in the mean, unconditionally (ledger 696)

`registryStrain_integral_isLittleO` (695) gives `∫₀ᵀ q_c = o(T)` for the prime-forced strain.  Littlewood's compiled
bound gives `|∫₀ᵀ S_all| ≤ C(1 + log(1+T))`, also `o(T)`.  Hence, unconditionally:

* `littlewood_integral_isLittleO` : `∫₀ᵀ S_all = o(T)`;
* `SAll_sub_registryStrain_isLittleO` : **`∫₀ᵀ S_all − ∫₀ᵀ q_c = o(T)`** — the full registration gap and the
  prime-forced strain have the same cumulative warp to `o(T)`;
* `smult_sub_registryStrain_add_offline_isLittleO` : **`(∫₀ᵀ S_mult − ∫₀ᵀ q_c) + ∫₀ᵀ N_off = o(T)`** — the crossing
  ledger's cumulative warp is the prime-forced one minus the off-line depth, to `o(T)`;
* `smultIntegralSublinear_iff_offline_mean` : the averaged door's hypothesis is exactly `∫₀ᵀ N_off = o(T)`.
-/

open Filter Topology Asymptotics MeasureTheory
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.ResidueJump

namespace CriticalLinePhasor.DVP

/-- The integrated off-line depth. -/
noncomputable def offInt (T : ℝ) : ℝ := ∫ t in (0:ℝ)..T, (offLineStripZeroCountMult t : ℝ)

/-- **Littlewood's bound is sublinear:** `∫₀ᵀ S_all = o(T)`. -/
theorem littlewood_integral_isLittleO :
    (fun T => ∫ t in (0:ℝ)..T, SAll t) =o[atTop] (fun T : ℝ => T) := by
  obtain ⟨C, hC⟩ := littlewoodBound_holds
  apply IsLittleO.of_bound
  intro ε hε
  have hCpos : (0:ℝ) < |C| + 1 := by positivity
  have hlog : ∀ᶠ T in atTop, Real.log (1 + T) ≤ (ε / (2 * (|C| + 1))) * (1 + T) := by
    have hsmall := Real.isLittleO_log_id_atTop.bound (c := ε / (2 * (|C| + 1))) (by positivity)
    have hten : Tendsto (fun T : ℝ => 1 + T) atTop atTop := by
      simpa [add_comm] using (tendsto_id.atTop_add (tendsto_const_nhds (x := (1:ℝ))))
    filter_upwards [hten.eventually hsmall, eventually_ge_atTop (0:ℝ)] with T hT hT0
    have hpos : 0 ≤ Real.log (1 + T) := Real.log_nonneg (by linarith)
    simp only [id, Real.norm_eq_abs, abs_of_nonneg hpos,
      abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 + T)] at hT
    exact hT
  filter_upwards [hlog, eventually_ge_atTop (2 * (|C| + 1) * (1 + 1 / ε) + 1)] with T hTlog hTbig
  have hεinv : 0 < 1 / ε := by positivity
  have hT0 : (0:ℝ) ≤ T := by nlinarith
  have hlog0 : 0 ≤ Real.log (1 + T) := Real.log_nonneg (by linarith)
  have hLW := hC T hT0
  have habs : |∫ t in (0:ℝ)..T, SAll t| ≤ |C| * (1 + Real.log (1 + T)) := by
    calc |∫ t in (0:ℝ)..T, SAll t| ≤ C * (1 + Real.log (1 + T)) := hLW
      _ ≤ |C| * (1 + Real.log (1 + T)) := by gcongr; exact le_abs_self C
  have habsC : (0:ℝ) ≤ |C| := abs_nonneg C
  have hmul : |C| * Real.log (1 + T) ≤ (ε / 2) * (1 + T) := by
    have h1 : |C| * Real.log (1 + T) ≤ |C| * ((ε / (2 * (|C| + 1))) * (1 + T)) :=
      mul_le_mul_of_nonneg_left hTlog habsC
    have h2 : |C| * ((ε / (2 * (|C| + 1))) * (1 + T)) = (|C| / (|C| + 1)) * ((ε / 2) * (1 + T)) := by
      field_simp
    have h3 : |C| / (|C| + 1) ≤ 1 := by
      rw [div_le_one hCpos]; linarith
    have h5 : (0:ℝ) ≤ (ε / 2) * (1 + T) := by positivity
    have h4 : (|C| / (|C| + 1)) * ((ε / 2) * (1 + T)) ≤ 1 * ((ε / 2) * (1 + T)) :=
      mul_le_mul_of_nonneg_right h3 h5
    rw [h2] at h1
    linarith
  have hinv : ε * (1 / ε) = 1 := by field_simp
  have hmulT : (ε / 2) * (2 * (|C| + 1) * (1 + 1 / ε) + 1) ≤ (ε / 2) * T :=
    mul_le_mul_of_nonneg_left hTbig (by positivity)
  have hexp : (ε / 2) * (2 * (|C| + 1) * (1 + 1 / ε) + 1)
      = ε * (|C| + 1) + (|C| + 1) * (ε * (1 / ε)) + ε / 2 := by ring
  rw [hexp, hinv, mul_one] at hmulT
  have hεK : ε ≤ ε * (|C| + 1) := by nlinarith
  have hexpand : |C| * (1 + Real.log (1 + T)) = |C| + |C| * Real.log (1 + T) := by ring
  rw [hexpand] at habs
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hT0]
  linarith

/-- **The full registration gap and the prime-forced strain have the same cumulative warp, to `o(T)`.** -/
theorem SAll_sub_registryStrain_isLittleO {c : ℝ} (hc : 0 < c) (hc1 : c < 1) :
    (fun T => (∫ t in (0:ℝ)..T, SAll t) - ∫ t in (0:ℝ)..T, registryStrain c t) =o[atTop] (fun T : ℝ => T) :=
  littlewood_integral_isLittleO.sub (registryStrain_integral_isLittleO hc hc1)

/-- **The crossing ledger's cumulative warp is the prime-forced one minus the off-line depth, to `o(T)`.** -/
theorem smult_sub_registryStrain_add_offline_isLittleO {c : ℝ} (hc : 0 < c) (hc1 : c < 1) :
    (fun T => ((∫ t in (0:ℝ)..T, Smult t) - ∫ t in (0:ℝ)..T, registryStrain c t) + offInt T)
      =o[atTop] (fun T : ℝ => T) := by
  refine (SAll_sub_registryStrain_isLittleO hc hc1).congr' (Eventually.of_forall fun T => ?_) EventuallyEq.rfl
  simp only [offInt, integral_smult_split T]
  ring

/-- **The averaged door's hypothesis is exactly the sublinearity of the off-line depth.** -/
theorem smultIntegralSublinear_iff_offline_mean :
    SmultIntegralSublinear ↔ ∀ ε : ℝ, 0 < ε → ∀ᶠ T in atTop, offInt T ≤ ε * T := by
  constructor
  · intro h ε hε
    have hL := littlewood_integral_isLittleO.bound (c := ε / 2) (by positivity)
    filter_upwards [h (ε / 2) (by positivity), hL, eventually_ge_atTop (0:ℝ)] with T hS hLT hT0
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hT0] at hLT
    have h1 : ∫ t in (0:ℝ)..T, SAll t ≤ (ε / 2) * T := le_trans (le_abs_self _) hLT
    simp only [offInt]
    have := integral_smult_split T
    linarith
  · intro h ε hε
    have hL := littlewood_integral_isLittleO.bound (c := ε / 2) (by positivity)
    filter_upwards [h (ε / 2) (by positivity), hL, eventually_ge_atTop (0:ℝ)] with T hN hLT hT0
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hT0] at hLT
    have h1 : -((ε / 2) * T) ≤ ∫ t in (0:ℝ)..T, SAll t := neg_le_of_abs_le hLT
    simp only [offInt] at hN
    have := integral_smult_split T
    linarith

/-! ## The door with no chart object in it

`N_off` is a chart quantity (ζ's strip zeros).  Eliminating it leaves a statement whose two sides are both fiber
quantities: the prime-forced cumulative warp `∫₀ᵀ q_c` (primes fuel S) and the crossing ledger's cumulative warp
`∫₀ᵀ S_mult` (the fiber's events on the line, against the clock). -/

/-- **The prime side and the crossing side agree in the mean.** -/
def PrimeCrossingMeanAgreement (c : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ T in atTop,
    (∫ t in (0:ℝ)..T, registryStrain c t) - (∫ t in (0:ℝ)..T, Smult t) ≤ ε * T

/-- **RH from the agreement of the two fiber ledgers in the mean.**  No zero set, no off-line count, no strip:
the hypothesis compares the prime-forced strain with the crossings. -/
theorem rh_of_primeCrossingMeanAgreement {c : ℝ} (hc : 0 < c) (hc1 : c < 1)
    (h : PrimeCrossingMeanAgreement c) : RiemannHypothesis := by
  apply rh_of_smultIntegralSublinear
  intro ε hε
  have hq := (registryStrain_integral_isLittleO hc hc1).bound (c := ε / 2) (by positivity)
  filter_upwards [h (ε / 2) (by positivity), hq, eventually_ge_atTop (0:ℝ)] with T hA hQ hT0
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hT0] at hQ
  have h1 : -((ε / 2) * T) ≤ ∫ t in (0:ℝ)..T, registryStrain c t := neg_le_of_abs_le hQ
  linarith


/-- Under RH the off-line ledger vanishes identically. -/
theorem offLineStripZeroCountMult_eq_zero_of_rh (hRH : RiemannHypothesis) (T : ℝ) :
    offLineStripZeroCountMult T = 0 := by
  unfold offLineStripZeroCountMult
  apply Finset.sum_eq_zero
  intro ρ hρ
  exfalso
  obtain ⟨hmem, hoff⟩ := Finset.mem_filter.mp hρ
  exact hoff (CriticalLinePhasor.Source.re_eq_half_of_rh hRH
    ((stripZeroWindow_finite T).mem_toFinset.mp hmem).1)

theorem primeCrossingMeanAgreement_of_rh {c : ℝ} (hc : 0 < c) (hc1 : c < 1)
    (hRH : RiemannHypothesis) : PrimeCrossingMeanAgreement c := by
  intro ε hε
  have hzero : ∀ T : ℝ, (∫ t in (0:ℝ)..T, (offLineStripZeroCountMult t : ℝ)) = 0 := by
    intro T
    have : ∀ t : ℝ, ((offLineStripZeroCountMult t : ℕ) : ℝ) = 0 := by
      intro t; rw [offLineStripZeroCountMult_eq_zero_of_rh hRH t]; simp
    simp [this]
  have hq := (registryStrain_integral_isLittleO hc hc1).bound (c := ε / 2) (by positivity)
  have hL := littlewood_integral_isLittleO.bound (c := ε / 2) (by positivity)
  filter_upwards [hq, hL, eventually_ge_atTop (0:ℝ)] with T hQ hLT hT0
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hT0] at hQ hLT
  have h1 : ∫ t in (0:ℝ)..T, registryStrain c t ≤ (ε / 2) * T := le_trans (le_abs_self _) hQ
  have h2 : -((ε / 2) * T) ≤ ∫ t in (0:ℝ)..T, SAll t := neg_le_of_abs_le hLT
  have h3 := integral_smult_split T
  rw [hzero T] at h3
  linarith

/-- **The agreement is exactly the Riemann Hypothesis** — no slack. -/
theorem primeCrossingMeanAgreement_iff_rh {c : ℝ} (hc : 0 < c) (hc1 : c < 1) :
    PrimeCrossingMeanAgreement c ↔ RiemannHypothesis :=
  ⟨rh_of_primeCrossingMeanAgreement hc hc1, primeCrossingMeanAgreement_of_rh hc hc1⟩


end CriticalLinePhasor.DVP

#print axioms CriticalLinePhasor.DVP.littlewood_integral_isLittleO
#print axioms CriticalLinePhasor.DVP.SAll_sub_registryStrain_isLittleO
#print axioms CriticalLinePhasor.DVP.smult_sub_registryStrain_add_offline_isLittleO
#print axioms CriticalLinePhasor.DVP.smultIntegralSublinear_iff_offline_mean
#print axioms CriticalLinePhasor.DVP.rh_of_primeCrossingMeanAgreement
#print axioms CriticalLinePhasor.DVP.primeCrossingMeanAgreement_iff_rh
