import RequestProject.HerglotzSweep

/-!
# The ladder at one anchor, part 1: definitions and the atomic Gram identity (ledger 630)

At an anchor `s` off the line and off the zero set, the transported measure of the nontrivial zeros has
coefficient sequence `μ_k = Σ_ρ m_ρ ω_ρ w_ρ^k` (`xiCoeff`), `ω_ρ = 1/((s−ρ)(ρ−c))`, `w_ρ = (ρ−c)/(s−ρ)`.
The **ladder** at `s` is the positivity of every Toeplitz form of the Hermitian extension of this sequence
(`Ladder`). For a positive unimodular atomic measure the Gram identity makes every Toeplitz form real and
nonnegative (`toeplitzForm_atomCoeffI_nonneg`); at an on-line zero `ω_ρ = 1/|s−ρ|²`
(`atomWeight_eq_of_online`), and the line weights are summable (`summable_lineWeight`).  The door
`ladder ⟹` every zero on the line is part 2.
-/

open Complex Finset

namespace CriticalLinePhasor.SeatingLedger

/-- The transported measure's coefficient sequence at anchor `s`. -/
noncomputable def xiCoeff (s : ℂ) (k : ℕ) : ℂ :=
  ∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
    (ZD.xiOrderNat ρ.val : ℂ) * atomWeight s ρ.val * transport s ρ.val ^ k

/-- The ladder at `s`: every Toeplitz form of the Hermitian-extended coefficients is real and `≥ 0`. -/
def Ladder (s : ℂ) : Prop :=
  ∀ (N : ℕ) (c : Fin N → ℂ),
    (toeplitzForm (hermExt (xiCoeff s)) c).im = 0 ∧ 0 ≤ (toeplitzForm (hermExt (xiCoeff s)) c).re

/-- The Riemann Hypothesis in the seat's zero set. -/
def RH : Prop := ∀ ρ ∈ ZD.NontrivialZeros, ρ.re = 1 / 2

/-! ## The Gram identity for a positive unimodular measure, any index type -/

section GenericGram
variable {ι : Type*} {ω : ι → ℝ} {w : ι → ℂ}

/-- Fourier coefficients of the positive unimodular measure `Σ_i ω_i δ_{w_i}`. -/
noncomputable def atomCoeffI (ω : ι → ℝ) (w : ι → ℂ) (k : ℤ) : ℂ := ∑' i, (ω i : ℂ) * w i ^ k

theorem summable_atomI (hs : Summable ω) (hw : ∀ i, ‖w i‖ = 1) (k : ℤ) :
    Summable (fun i => (ω i : ℂ) * w i ^ k) := by
  refine Summable.of_norm_bounded hs.abs (fun i => le_of_eq ?_)
  rw [norm_mul, norm_zpow, hw, one_zpow, mul_one, Complex.norm_real, Real.norm_eq_abs]

theorem atom_ne_zeroI (hw : ∀ i, ‖w i‖ = 1) (i : ι) : w i ≠ 0 := by
  intro h
  have := hw i
  rw [h, norm_zero] at this
  exact zero_ne_one this

theorem atom_zpow_invI (hw : ∀ i, ‖w i‖ = 1) (i : ι) (k : ℤ) :
    (w i ^ k)⁻¹ = (starRingEnd ℂ) (w i ^ k) :=
  Complex.inv_eq_conj (by rw [norm_zpow, hw, one_zpow])

theorem atomCoeffI_conj (hs : Summable ω) (hw : ∀ i, ‖w i‖ = 1) (k : ℤ) :
    (starRingEnd ℂ) (atomCoeffI ω w k) = atomCoeffI ω w (-k) := by
  unfold atomCoeffI
  have h := ((summable_atomI hs hw k).hasSum.map (starRingEnd ℂ) Complex.continuous_conj).tsum_eq
  rw [← h]
  apply tsum_congr
  intro i
  simp only [Function.comp_apply, map_mul, Complex.conj_ofReal]
  rw [← atom_zpow_invI hw i k, zpow_neg]

theorem toeplitzForm_atomCoeffI (hs : Summable ω) (hw : ∀ i, ‖w i‖ = 1) {N : ℕ} (c : Fin N → ℂ) :
    toeplitzForm (atomCoeffI ω w) c
      = ∑' i, ((ω i * Complex.normSq (∑ j : Fin N, (starRingEnd ℂ) (c j) * w i ^ (j : ℤ)) : ℝ) : ℂ) := by
  unfold toeplitzForm atomCoeffI
  have hsum : ∀ (j l : Fin N), Summable (fun i =>
      (starRingEnd ℂ) (c j) * c l * ((ω i : ℂ) * w i ^ ((j : ℤ) - (l : ℤ)))) :=
    fun j l => (summable_atomI hs hw _).mul_left _
  have step1 : ∀ j : Fin N,
      ∑ l : Fin N, (starRingEnd ℂ) (c j) * c l * ∑' i, (ω i : ℂ) * w i ^ ((j : ℤ) - (l : ℤ))
        = ∑' i, ∑ l : Fin N, (starRingEnd ℂ) (c j) * c l * ((ω i : ℂ) * w i ^ ((j : ℤ) - (l : ℤ))) := by
    intro j
    rw [Summable.tsum_finsetSum (fun l _ => hsum j l)]
    exact Finset.sum_congr rfl (fun l _ => (tsum_mul_left).symm)
  rw [Finset.sum_congr rfl (fun j _ => step1 j),
    ← Summable.tsum_finsetSum (fun j _ => summable_sum (fun l _ => hsum j l))]
  apply tsum_congr
  intro i
  have hterm : ∀ (j l : ℤ), (ω i : ℂ) * w i ^ (j - l)
      = (ω i : ℂ) * (w i ^ j * (starRingEnd ℂ) (w i ^ l)) := by
    intro j l
    rw [zpow_sub₀ (atom_ne_zeroI hw i), div_eq_mul_inv, atom_zpow_invI hw i l]
  simp_rw [hterm]
  rw [Complex.ofReal_mul, ← Complex.mul_conj, map_sum, Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  simp only [map_mul, Complex.conj_conj]
  ring

theorem toeplitzForm_atomCoeffI_nonneg (hω : ∀ i, 0 ≤ ω i) (hs : Summable ω)
    (hw : ∀ i, ‖w i‖ = 1) {N : ℕ} (c : Fin N → ℂ) :
    (toeplitzForm (atomCoeffI ω w) c).im = 0 ∧ 0 ≤ (toeplitzForm (atomCoeffI ω w) c).re := by
  rw [toeplitzForm_atomCoeffI hs hw c, ← Complex.ofReal_tsum]
  refine ⟨Complex.ofReal_im _, ?_⟩
  rw [Complex.ofReal_re]
  exact tsum_nonneg (fun i => mul_nonneg (hω i) (Complex.normSq_nonneg _))

end GenericGram

/-! ## The weights of the zeros -/

/-- On the line, the transported weight is `1/|s−ρ|²`, a positive real. -/
theorem atomWeight_eq_of_online {s ρ : ℂ} (hρ : ρ.re = 1 / 2) :
    atomWeight s ρ = (((Complex.normSq (s - ρ))⁻¹ : ℝ) : ℂ) := by
  unfold atomWeight
  rw [sub_mirror_eq_conj hρ, Complex.mul_conj, Complex.ofReal_inv]

/-- An anchor off the zero set has a zero-free ball around it. -/
theorem exists_zero_free_ball {s : ℂ} (hs : s ∉ ZD.NontrivialZeros) :
    ∃ δ > 0, ∀ ρ ∈ ZD.NontrivialZeros, δ ≤ ‖s - ρ‖ := by
  have hne : ZD.riemannXi s ≠ 0 := fun h => hs ((ZD.riemannXi_eq_zero_iff s).mp h)
  have hev := (ZD.ZeroCount.riemannXi_continuous.continuousAt (x := s)).eventually_ne hne
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨ε, hε, hball⟩ := hev
  refine ⟨ε, hε, fun ρ hρ => ?_⟩
  by_contra hlt
  push Not at hlt
  have hρ0 : ZD.riemannXi ρ = 0 := (ZD.riemannXi_eq_zero_iff ρ).mpr hρ
  exact hball (by rw [dist_eq_norm, norm_sub_rev]; exact hlt) hρ0

/-- `1/|s−ρ|² ≤ C/|ρ|²` uniformly over the zeros, for `s` off the zero set. -/
theorem inv_normSq_sub_le {s : ℂ} (hs : s ∉ ZD.NontrivialZeros) :
    ∃ C : ℝ, ∀ ρ ∈ ZD.NontrivialZeros,
      (Complex.normSq (s - ρ))⁻¹ ≤ C * (1 / ‖ρ‖ ^ 2) := by
  obtain ⟨δ, hδ, hball⟩ := exists_zero_free_ball hs
  set κ : ℝ := δ / (‖s‖ + δ) with hκ
  have hκpos : 0 < κ := by positivity
  refine ⟨1 / κ ^ 2, fun ρ hρ => ?_⟩
  have hρne : ρ ≠ 0 := by
    intro h; rw [h] at hρ; obtain ⟨h1, -, -⟩ := hρ; simp at h1
  have hρpos : 0 < ‖ρ‖ := norm_pos_iff.mpr hρne
  have hlow : κ * ‖ρ‖ ≤ ‖s - ρ‖ := by
    rcases le_or_gt ‖ρ‖ (‖s‖ + δ) with h | h
    · calc κ * ‖ρ‖ ≤ κ * (‖s‖ + δ) := by gcongr
        _ = δ := by rw [hκ]; field_simp
        _ ≤ ‖s - ρ‖ := hball ρ hρ
    · have h1 : ‖ρ‖ - ‖s‖ ≤ ‖s - ρ‖ := by
        have := norm_sub_norm_le ρ s
        rw [norm_sub_rev] at this; linarith
      have h2 : κ * ‖ρ‖ ≤ ‖ρ‖ - ‖s‖ := by
        rw [hκ, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith [norm_nonneg s]
      linarith
  have hsq : (κ * ‖ρ‖) ^ 2 ≤ Complex.normSq (s - ρ) := by
    rw [Complex.normSq_eq_norm_sq]
    exact pow_le_pow_left₀ (by positivity) hlow 2
  have hpos : 0 < (κ * ‖ρ‖) ^ 2 := by positivity
  calc (Complex.normSq (s - ρ))⁻¹ ≤ ((κ * ‖ρ‖) ^ 2)⁻¹ := by gcongr
    _ = 1 / κ ^ 2 * (1 / ‖ρ‖ ^ 2) := by rw [mul_pow]; field_simp

/-- The line weights `m_ρ/|s−ρ|²` are summable. -/
theorem summable_lineWeight {s : ℂ} (hs : s ∉ ZD.NontrivialZeros) :
    Summable (fun ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} =>
      (ZD.xiOrderNat ρ.val : ℝ) * (Complex.normSq (s - ρ.val))⁻¹) := by
  obtain ⟨C, hC⟩ := inv_normSq_sub_le hs
  have hbase := ZD.summable_xiOrderNat_div_norm_sq_nontrivialZeros
  refine Summable.of_nonneg_of_le (fun ρ => ?_) (fun ρ => ?_) (hbase.mul_left C)
  · exact mul_nonneg (Nat.cast_nonneg _) (inv_nonneg.mpr (Complex.normSq_nonneg _))
  · calc (ZD.xiOrderNat ρ.val : ℝ) * (Complex.normSq (s - ρ.val))⁻¹
        ≤ (ZD.xiOrderNat ρ.val : ℝ) * (C * (1 / ‖ρ.val‖ ^ 2)) := by
          gcongr; exact hC ρ.val ρ.property
      _ = C * ((ZD.xiOrderNat ρ.val : ℝ) / ‖ρ.val‖ ^ 2) := by ring

end CriticalLinePhasor.SeatingLedger

#print axioms CriticalLinePhasor.SeatingLedger.toeplitzForm_atomCoeffI_nonneg
#print axioms CriticalLinePhasor.SeatingLedger.summable_lineWeight
