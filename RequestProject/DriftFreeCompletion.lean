import RequestProject.SitesVersusContinuum

/-!
# The drift-free completion of the sites, and where δ-independent positivity lands (ledger 1227)

Sam's question (2026-10-11): does structure already present in the native construction make the physical
spectral space a positive quotient/completion of the exhaustive generalized spectral realization, for reasons
independent of `δ`? This file computes the native site completion exactly.

**The drift-free normalization.** `driftMass N = Σ_{n≤N} 1/n`. Dividing the site pairing by it is the native
normalization of the area-measure delta (the area pairing of zero-states is only distributional; on sites
its divergence is exactly `driftMass N`).

* `partner_pairing_normalized`: the bank at `ρ` and the bank at its same-height partner `ρ*` pair to exactly `1`,
  every `N`, every `ρ`. This positive number does not depend on `δ` or on the height.
* `selfPairing_eq_bankMass`: the self-pairing of the bank depends on `ρ` only through `Re ρ`. Site-diagonal forms
  are blind to cancellation: they never use `ζ(ρ) = 0`.
* `selfMass_half`: on the line the normalized self-mass is exactly `1`, every `N`.
* `selfMass_tendsto_zero` (`σ > ½`) and `selfMass_tendsto_top` (`σ < ½`): off the line the normalized self-mass
  goes to `0` (the state becomes null) or to `∞` (the state leaves the space).
* `selfMass_partner_product` (Cauchy–Schwarz): `selfMass σ · selfMass (1 − σ) ≥ 1 = (partner pairing)²`.

So in the native site completion the `δ`-independent positive mass sits in the PARTNER slot, and the diagonal
(survival) is computed from `σ` alone. The survival criterion is `σ = ½` with no input from the cancellation.

* `partner_identification_invariant`: the physical-state condition "identify each state with its partner"
  (`v ~ w`) is invariant under a generator with `T v = a v`, `T w = b w` only if `a = b`. For partners
  `b = conj a`, so this quotient exists only at real eigenvalue.
-/

open Complex Finset Filter Topology

noncomputable section

namespace CriticalLinePhasor.DriftFreeCompletion

open CriticalLinePhasor.SameHeight CriticalLinePhasor.SitesContinuum

/-- The drift-free mass `H_N = Σ_{n≤N} 1/n`. -/
def driftMass (N : ℕ) : ℝ := ∑ n ∈ Finset.Icc 1 N, ((n : ℝ))⁻¹

/-- The self-mass of the bank at abscissa `σ`: `Σ_{n≤N} n^{−2σ}`. -/
def bankMass (σ : ℝ) (N : ℕ) : ℝ := ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-2 * σ)

/-- The self-mass in the drift-free normalization. -/
def selfMass (σ : ℝ) (N : ℕ) : ℝ := bankMass σ N / driftMass N

theorem driftMass_nonneg (N : ℕ) : 0 ≤ driftMass N :=
  Finset.sum_nonneg fun n _ => inv_nonneg.mpr (Nat.cast_nonneg n)

theorem driftMass_pos {N : ℕ} (hN : 1 ≤ N) : 0 < driftMass N :=
  Finset.sum_pos
    (fun n hn => inv_pos.mpr (Nat.cast_pos.mpr (by have := (Finset.mem_Icc.mp hn).1; omega)))
    ⟨1, Finset.mem_Icc.mpr ⟨le_refl 1, hN⟩⟩

theorem driftMass_tendsto : Tendsto driftMass atTop atTop := by
  have hlog : Tendsto (fun N : ℕ => Real.log ((N + 1 : ℕ) : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  refine tendsto_atTop_mono (fun N => ?_) hlog
  have he : ((harmonic N : ℚ) : ℝ) = driftMass N := by
    simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, driftMass]
  rw [← he]
  exact log_add_one_le_harmonic N

theorem selfMass_nonneg (σ : ℝ) (N : ℕ) : 0 ≤ selfMass σ N :=
  div_nonneg (Finset.sum_nonneg fun n _ => Real.rpow_nonneg (Nat.cast_nonneg n) _) (driftMass_nonneg N)

/-- **Site-diagonal forms are cancellation-blind.** -/
theorem selfPairing_eq_bankMass (N : ℕ) (ρ : ℂ) :
    ∑ n ∈ Finset.Icc 1 N, ‖(n : ℂ) ^ (-ρ)‖ ^ 2 = bankMass ρ.re N := by
  unfold bankMass
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn1 : 0 < n := by have := (Finset.mem_Icc.mp hn).1; omega
  rw [Complex.norm_natCast_cpow_of_pos hn1, ← Real.rpow_natCast,
    ← Real.rpow_mul (Nat.cast_nonneg n), Complex.neg_re]
  congr 1
  push_cast
  ring

/-- **The partner pairing in the drift-free normalization is exactly `1`, for every `ρ`.** -/
theorem partner_pairing_normalized {N : ℕ} (hN : 1 ≤ N) (ρ : ℂ) :
    (∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-ρ) * (starRingEnd ℂ) ((n : ℂ) ^ (-(partner ρ)))) /
      (driftMass N : ℂ) = 1 := by
  have h : (∑ n ∈ Finset.Icc 1 N, (((n : ℝ))⁻¹ : ℂ)) = (driftMass N : ℂ) := by
    simp only [driftMass, Complex.ofReal_sum, Complex.ofReal_inv]
  rw [partner_pairing_eq_harmonic, h]
  exact div_self (Complex.ofReal_ne_zero.mpr (driftMass_pos hN).ne')

/-- **On the line the normalized self-mass is exactly `1`.** -/
theorem selfMass_half {N : ℕ} (hN : 1 ≤ N) : selfMass (1 / 2) N = 1 := by
  have h : bankMass (1 / 2) N = driftMass N := by
    unfold bankMass driftMass
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [show (-2 * (1 / 2 : ℝ)) = -1 by norm_num, Real.rpow_neg_one]
  unfold selfMass
  rw [h, div_self (driftMass_pos hN).ne']

theorem bankMass_le_tsum {σ : ℝ} (hσ : 1 / 2 < σ) (N : ℕ) :
    bankMass σ N ≤ ∑' n : ℕ, (n : ℝ) ^ (-2 * σ) := by
  have hs : Summable (fun n : ℕ => (n : ℝ) ^ (-2 * σ)) := Real.summable_nat_rpow.mpr (by linarith)
  exact Summable.sum_le_tsum _ (fun n _ => Real.rpow_nonneg (Nat.cast_nonneg n) _) hs

/-- **Right of the line the state becomes null.** -/
theorem selfMass_tendsto_zero {σ : ℝ} (hσ : 1 / 2 < σ) : Tendsto (selfMass σ) atTop (𝓝 0) := by
  have hlim : Tendsto (fun N => (∑' n : ℕ, (n : ℝ) ^ (-2 * σ)) / driftMass N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop driftMass_tendsto
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun N => selfMass_nonneg σ N) ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact div_le_div_of_nonneg_right (bankMass_le_tsum hσ N) (driftMass_pos hN).le

/-- **Cauchy–Schwarz between a state and its partner.** -/
theorem partner_mass_product (N : ℕ) (σ : ℝ) :
    driftMass N ^ 2 ≤ bankMass σ N * bankMass (1 - σ) N := by
  have key := Finset.sum_mul_sq_le_sq_mul_sq (Finset.Icc 1 N)
    (fun n : ℕ => (n : ℝ) ^ (-σ)) (fun n : ℕ => (n : ℝ) ^ (-(1 - σ)))
  have h1 : ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-σ) * (n : ℝ) ^ (-(1 - σ)) = driftMass N := by
    unfold driftMass
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (by have := (Finset.mem_Icc.mp hn).1; omega)
    rw [← Real.rpow_add hn0, show -σ + -(1 - σ) = (-1 : ℝ) by ring, Real.rpow_neg_one]
  have hsq : ∀ (a : ℝ) (n : ℕ), ((n : ℝ) ^ (-a)) ^ 2 = (n : ℝ) ^ (-2 * a) := fun a n => by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n)]
    congr 1
    push_cast
    ring
  simp only [hsq] at key
  rw [h1] at key
  exact key

theorem selfMass_partner_product {N : ℕ} (hN : 1 ≤ N) (σ : ℝ) :
    1 ≤ selfMass σ N * selfMass (1 - σ) N := by
  have hH := driftMass_pos hN
  unfold selfMass
  rw [div_mul_div_comm, le_div_iff₀ (mul_pos hH hH), one_mul, ← sq]
  exact partner_mass_product N σ

/-- **Left of the line the state leaves the space.** -/
theorem selfMass_tendsto_top {σ : ℝ} (hσ : σ < 1 / 2) : Tendsto (selfMass σ) atTop atTop := by
  have h0 : Tendsto (selfMass (1 - σ)) atTop (𝓝 0) := selfMass_tendsto_zero (by linarith)
  have hpos : ∀ᶠ N in atTop, 0 < selfMass (1 - σ) N := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hp := selfMass_partner_product hN σ
    have hn := selfMass_nonneg σ N
    rcases le_or_gt (selfMass (1 - σ) N) 0 with h | h
    · nlinarith
    · exact h
  have hinv : Tendsto (fun N => (selfMass (1 - σ) N)⁻¹) atTop atTop :=
    tendsto_inv_nhdsGT_zero.comp (tendsto_nhdsWithin_iff.mpr ⟨h0, hpos⟩)
  refine tendsto_atTop_mono' atTop ?_ hinv
  filter_upwards [eventually_ge_atTop 1, hpos] with N hN hp
  rw [inv_eq_one_div, div_le_iff₀ hp]
  exact selfMass_partner_product hN σ

/-- **Identifying a state with its partner is generator-invariant only at equal eigenvalues.** -/
theorem partner_identification_invariant {E : Type*} [AddCommGroup E] [Module ℂ E]
    (T : E →ₗ[ℂ] E) {v w : E} {a b c : ℂ} (hli : LinearIndependent ℂ ![v, w])
    (hv : T v = a • v) (hw : T w = b • w) (hc : T (v - w) = c • (v - w)) : a = b := by
  rw [map_sub, hv, hw] at hc
  have h0 : (a - c) • v + (c - b) • w = 0 := by
    have : (a - c) • v + (c - b) • w = (a • v - b • w) - c • (v - w) := by
      simp only [sub_smul, smul_sub]
      abel
    rw [this, hc, sub_self]
  obtain ⟨h1, h2⟩ := LinearIndependent.pair_iff.mp hli _ _ h0
  linear_combination h1 + h2

end CriticalLinePhasor.DriftFreeCompletion

end

#print axioms CriticalLinePhasor.DriftFreeCompletion.driftMass_tendsto
#print axioms CriticalLinePhasor.DriftFreeCompletion.selfPairing_eq_bankMass
#print axioms CriticalLinePhasor.DriftFreeCompletion.partner_pairing_normalized
#print axioms CriticalLinePhasor.DriftFreeCompletion.selfMass_half
#print axioms CriticalLinePhasor.DriftFreeCompletion.selfMass_tendsto_zero
#print axioms CriticalLinePhasor.DriftFreeCompletion.selfMass_partner_product
#print axioms CriticalLinePhasor.DriftFreeCompletion.selfMass_tendsto_top
#print axioms CriticalLinePhasor.DriftFreeCompletion.partner_identification_invariant
