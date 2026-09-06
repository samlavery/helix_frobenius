import RequestProject.RieszTruncatedFormula
import RequestProject.FinitePartSymmetry
import RequestProject.SeatMassEtaForm
import RequestProject.PrimeStrain

/-!
# The registration mechanism at the density level (ledger 607): there is no residual

On the line `s₀ = ½ + it`, at a good height, the compiled Riesz truncated formula (563–568) reads,
after taking real parts:

  `Σ_ρ m_ρ Re K_L(ρ − s₀) = clockRate t + Re[K_L(1−s₀) + K_L(−s₀) + rem_L(s₀)] − Re P_L(s₀)`

(`density_on_line`). Two compiled facts make the left side the smoothed ZERO density alone: `Re ξ′/ξ = 0`
on the line (593), and `Re(weilEnds + weilClock)(½+it) = clockRate t` (`re_weilArch_line`: the two
pole terms have opposite real parts on the line, and the rest is the Γ-clock rate of
`CarrierScaleCompensation`). `P_L` is the Riesz-tapered prime bank, a FINITE sum
(`rieszPrimeSum_eq_finset`), and `rem_L` is the explicit archimedean Riesz remainder
(`rieszClockRemainder`).

So the Fejér-smoothed zero density at height `t` is the clock rate plus the prime bank plus explicit
remainders — the registration operator's own equation, with no term left over. The Riesz strain
`rieszStrain L` is the `t`-antiderivative of `−Re P_L/π` (`rieszStrain_hasDerivAt`), so integrating
this identity over a station gap of the Riesz-strained clock gives a smoothed count of exactly one
plus the integrated remainders: the next theorem.
-/

open Complex Set MeasureTheory Filter Topology
open scoped Interval Real
open CriticalLinePhasor.CarrierScale (clockRate line lineC)

namespace CriticalLinePhasor.ContourArgument

/-! ## 1. The archimedean pieces on the line -/

/-- On the line the two pole terms have opposite real parts. -/
theorem re_weilEnds_line (t : ℝ) :
    (weilEnds (1 / 2 + (t : ℂ) * I)).re = -(Real.log Real.pi) / 2 := by
  unfold weilEnds
  have hz1 : (1 / 2 + (t : ℂ) * I).re = 1 / 2 := by simp
  have hz1' : (1 / 2 + (t : ℂ) * I).im = t := by simp
  have hz2 : (1 / 2 + (t : ℂ) * I - 1).re = -(1 / 2) := by simp; norm_num
  have hz2' : (1 / 2 + (t : ℂ) * I - 1).im = t := by simp
  have hn1 : Complex.normSq (1 / 2 + (t : ℂ) * I) = (1 / 2) ^ 2 + t ^ 2 := by
    rw [Complex.normSq_apply, hz1, hz1']; ring
  have hn2 : Complex.normSq (1 / 2 + (t : ℂ) * I - 1) = (1 / 2) ^ 2 + t ^ 2 := by
    rw [Complex.normSq_apply, hz2, hz2']; ring
  have e1 : (1 / (1 / 2 + (t : ℂ) * I)).re = (1 / 2) / ((1 / 2) ^ 2 + t ^ 2) := by
    rw [one_div, Complex.inv_re, hz1, hn1]
  have e2 : (1 / (1 / 2 + (t : ℂ) * I - 1)).re = (-(1 / 2)) / ((1 / 2) ^ 2 + t ^ 2) := by
    rw [one_div, Complex.inv_re, hz2, hn2]
  have e3 : (((Real.log Real.pi : ℝ) : ℂ) / 2).re = Real.log Real.pi / 2 := by
    simp
  rw [Complex.sub_re, Complex.add_re, e1, e2, e3]
  ring

/-- `Re(weilEnds + weilClock)(½ + it) = clockRate t`: the ends and the Γ-clock ARE the clock rate. -/
theorem re_weilArch_line (t : ℝ) :
    (weilEnds (1 / 2 + (t : ℂ) * I) + weilClock (1 / 2 + (t : ℂ) * I)).re = clockRate t := by
  have hre : (0 : ℝ) < (1 / 2 + (t : ℂ) * I).re := by simp
  have hG := CriticalLinePhasor.SeatingLedger.logDeriv_Gammaℝ_eq hre
  unfold clockRate line lineC
  rw [hG, Complex.add_re, re_weilEnds_line]
  unfold weilClock
  simp only [Complex.add_re, Complex.neg_re, Complex.div_ofNat_re, Complex.ofReal_re]

/-! ## 2. The finite prime bank and the Riesz strain -/

/-- The Riesz-tapered prime bank at `s₀`. -/
noncomputable def rieszPrimeSum (L : ℝ) (s₀ : ℂ) : ℂ :=
  ∑' n : ℕ, (rieszProfile L (Real.log n) : ℂ) * LSeries.term vonMangoldtC s₀ n

theorem rieszProfile_eq_zero_of_ge {L v : ℝ} (hL : 0 < L) (hv : L ≤ v) : rieszProfile L v = 0 := by
  rw [rieszProfile_eq hL (by linarith)]
  apply max_eq_right
  rw [sub_nonpos, one_le_div hL]
  exact hv

/-- The bank is a finite sum over `n ≤ ⌊e^L⌋`. -/
theorem rieszPrimeSum_eq_finset {L : ℝ} (hL : 0 < L) (s₀ : ℂ) :
    rieszPrimeSum L s₀
      = ∑ n ∈ Finset.range (⌊Real.exp L⌋₊ + 1),
          (rieszProfile L (Real.log n) : ℂ) * LSeries.term vonMangoldtC s₀ n := by
  unfold rieszPrimeSum
  apply tsum_eq_sum
  intro n hn
  rw [Finset.mem_range, not_lt] at hn
  have hnL : L ≤ Real.log n := by
    have h1 : Real.exp L < n := by
      have := Nat.lt_floor_add_one (Real.exp L)
      have h2 : (⌊Real.exp L⌋₊ : ℝ) + 1 ≤ n := by exact_mod_cast hn
      linarith
    have := Real.log_lt_log (Real.exp_pos L) h1
    rw [Real.log_exp] at this
    exact this.le
  rw [rieszProfile_eq_zero_of_ge hL hnL]
  simp

/-- The Riesz strain: the tapered prime-clock bank of `S`. -/
noncomputable def rieszStrain (L : ℝ) (t : ℝ) : ℝ :=
  -(1 / Real.pi) * ∑ n ∈ Finset.range (⌊Real.exp L⌋₊ + 1),
    rieszProfile L (Real.log n) * strainClock n t

theorem rieszStrain_continuous (L : ℝ) : Continuous (rieszStrain L) := by
  unfold rieszStrain
  exact continuous_const.mul
    (continuous_finset_sum _ (fun n _ => continuous_const.mul (strainClock_continuous n)))

theorem abs_rieszStrain_le (L : ℝ) (t : ℝ) :
    |rieszStrain L t| ≤ (1 / Real.pi) * ∑ n ∈ Finset.range (⌊Real.exp L⌋₊ + 1),
      |rieszProfile L (Real.log n)| * |strainAmp n| := by
  unfold rieszStrain
  rw [abs_mul, abs_neg, abs_of_pos (by positivity : (0:ℝ) < 1 / Real.pi)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun n _ => ?_))
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (abs_strainClock_le n t) (abs_nonneg _)

/-! ## 3. The density identity on the line -/

/-- The archimedean Riesz remainder: the clock line integrals minus the clock at the point. -/
noncomputable def rieszClockRemainder (L a b : ℝ) (s₀ : ℂ) : ℂ :=
  (1 / (2 * π)) * ((∫ τ : ℝ, rieszKernel L ((b : ℂ) + τ * I - s₀) * weilClock ((b : ℂ) + τ * I))
      + (∫ τ : ℝ, rieszKernel L ((a : ℂ) + τ * I - s₀) * weilClock (1 - ((a : ℂ) + τ * I))))
    - weilClock s₀

/-- A good height is not a zero ordinate, so `½ + it` is off the zeros. -/
theorem line_not_mem_zeros_of_goodHeight {t : ℝ} (ht : GoodHeight t) :
    (1 / 2 + (t : ℂ) * I) ∉ ZD.NontrivialZeros := by
  intro hmem
  have := ht.2 _ hmem
  simp at this

/-- **The registration density identity on the line.** At a good height `t`, for every Riesz
bandwidth `L > 0` and strip window `a < 0 < 1 < b`:

  `Re Σ'_ρ m_ρ K_L(ρ − s₀) = clockRate t + Re(K_L(1−s₀) + K_L(−s₀)) + Re rem_L − Re P_L(s₀)`,

`s₀ = ½ + it`. The `ξ′/ξ` term is absent: its real part vanishes on the line. -/
theorem density_on_line {L : ℝ} (hL : 0 < L) {t : ℝ} (ht : GoodHeight t) {a b : ℝ}
    (ha : a < 0) (hb : 1 < b) :
    (∑' ρ : Zero, (ZD.xiOrderNat ρ.val : ℂ)
        * rieszKernel L (ρ.val - (1 / 2 + (t : ℂ) * I))).re
      = clockRate t
        + (rieszKernel L (1 - (1 / 2 + (t : ℂ) * I)) + rieszKernel L (-(1 / 2 + (t : ℂ) * I))).re
        + (rieszClockRemainder L a b (1 / 2 + (t : ℂ) * I)).re
        - (rieszPrimeSum L (1 / 2 + (t : ℂ) * I)).re := by
  set s₀ : ℂ := 1 / 2 + (t : ℂ) * I with hs₀def
  have hs₀ : s₀ ∉ ZD.NontrivialZeros := line_not_mem_zeros_of_goodHeight ht
  have h0 : s₀ ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp [hs₀def] at this
  have h1 : s₀ ≠ 1 := by
    intro h; have := congrArg Complex.re h; simp [hs₀def] at this
  have hre : s₀.re = 1 / 2 := by simp [hs₀def]
  have hends := truncated_explicit_formula_riesz_ends hL hs₀ h0 h1 ha hb
    (by rw [hre]; linarith) (by rw [hre]; linarith)
  -- Re ξ′/ξ(s₀) = 0 on the line
  have hxi : (logDeriv ZD.riemannXi s₀).re = 0 := by
    rw [← xiFinitePart_eq_logDeriv hs₀]
    exact re_xiFinitePart_of_re_half hre
  have hre_arch := re_weilArch_line t
  -- rearrange the ends identity into the remainder form
  have hrem : (1 / (2 * π)) * ((∫ τ : ℝ, rieszKernel L ((b : ℂ) + τ * I - s₀) * weilClock ((b : ℂ) + τ * I))
      + (∫ τ : ℝ, rieszKernel L ((a : ℂ) + τ * I - s₀) * weilClock (1 - ((a : ℂ) + τ * I))))
      = weilClock s₀ + rieszClockRemainder L a b s₀ := by
    unfold rieszClockRemainder; ring
  rw [hrem] at hends
  have hP : rieszPrimeSum L s₀ = ∑' n : ℕ, (rieszProfile L (Real.log n) : ℂ) * LSeries.term vonMangoldtC s₀ n := rfl
  rw [← hP] at hends
  have key := congrArg Complex.re hends
  simp only [Complex.add_re, Complex.sub_re] at key
  rw [hxi] at key
  have harch : (weilEnds s₀).re + (weilClock s₀).re = clockRate t := by
    rw [← Complex.add_re]; exact hre_arch
  rw [Complex.add_re]
  linarith

end CriticalLinePhasor.ContourArgument

#print axioms CriticalLinePhasor.ContourArgument.re_weilArch_line
#print axioms CriticalLinePhasor.ContourArgument.rieszPrimeSum_eq_finset
#print axioms CriticalLinePhasor.ContourArgument.density_on_line
