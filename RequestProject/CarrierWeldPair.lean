import RequestProject.CarrierLatticeWeld

/-!
# The rank-uniform completed FE family: the matrix bank as a weak FE-pair at every rank

Certifier (a) of the standing wave, second brick — the analytic packaging of the
carrier-lattice weld.  The rank-`r` matrix bank `θ_r(t) = ∑_{A ∈ M_{r+1}(ℤ)} e^{-πt‖A‖²}`
(the compiled `matrixTheta` of `CarrierLatticeWeld`, cast to `ℂ`) is here packaged as a
Mathlib `WeakFEPair` at EVERY rank simultaneously — weight `k = (r+1)²/2`, root number `1`,
both constant terms the DC mode `1` of the matrix bank.  Mathlib's abstract
functional-equation machinery then returns, uniformly in `r`:

* the entire part `Λ₀` (`matrixWeld_entirePart_differentiable`);
* the completed functional equation `Λ((r+1)²/2 - s) = Λ^∨(s)`
  (`matrixWeld_functional_equation`);
* the two poles, at `s = (r+1)²/2` and `s = 0`, with residues `+1` and `-1` — the DC mode
  of the matrix bank entering and leaving the chart (`matrixWeld_residue_k`,
  `matrixWeld_residue_zero`).

The analytic inputs are proved here from the compiled weld and nothing else:

* the bank is antitone in the carrier height (`matrixTheta_antitoneOn`), hence locally
  integrable on the positive carrier axis (`matrixThetaC_locallyIntegrableOn`);
* the explicit tail bound `θ_r(t) - 1 ≤ C_r·e^{-πt}` for `t ≥ 1`, with the explicit
  constant `C_r = (r+1)²·S(1)^{(r+1)²-1}·2/(1-e^{-π})` (`matrixTheta_sub_one_le`,
  through the one-strand tail `strandTheta_sub_one_le` and the telescoping power bound
  `pow_sub_one_le_of_le`);
* hence superpolynomial decay of the tail at the top of the carrier
  (`matrixThetaC_sub_one_isBigO`).

This is the rank-uniform self-dual profile family on the carrier lattice — fiber-free: no
cusp form, no automorphy, no L-function enters; classical Poisson on a vector space
(through the compiled `matrixTheta_inv`) is the only analytic input.  Its role is the
self-dual side of certifier (a): the object the house pairs with the rung's arithmetic
profile.  That pairing — coupling this self-dual bank to a given rung's arithmetic
profile — is not done in this file.
-/

open Real Filter Set MeasureTheory Asymptotics Topology

namespace CriticalLinePhasor.CarrierWeldPair

open CriticalLinePhasor.CarrierLatticeWeld

/-! ## Monotonicity of the bank in the carrier height -/

/-- The single strand is antitone in the carrier height: each Gaussian phasor term only
loses mass as the height grows. -/
lemma strandTheta_anti {t₁ t₂ : ℝ} (h0 : 0 < t₁) (h : t₁ ≤ t₂) :
    strandTheta t₂ ≤ strandTheta t₁ := by
  refine Summable.tsum_le_tsum (fun n => ?_)
    (summable_gaussInt (h0.trans_le h)) (summable_gaussInt h0)
  apply Real.exp_le_exp.mpr
  nlinarith [mul_nonneg (mul_nonneg Real.pi_pos.le (sub_nonneg.mpr h))
    (sq_nonneg ((n : ℤ) : ℝ))]

/-- The matrix bank is antitone on the positive carrier axis, at every rank: the strand
power of an antitone strand with mass at least the DC mode. -/
lemma matrixTheta_antitoneOn (r : ℕ) : AntitoneOn (matrixTheta r) (Ioi (0 : ℝ)) := by
  intro t₁ ht₁ t₂ _ h
  rw [matrixTheta_eq_pow r ht₁, matrixTheta_eq_pow r (lt_of_lt_of_le ht₁ h)]
  exact pow_le_pow_left₀
    (le_trans zero_le_one (one_le_strandTheta (lt_of_lt_of_le ht₁ h)))
    (strandTheta_anti ht₁ h) _

/-! ## The complex-valued profile and its local integrability -/

/-- The complex-valued matrix bank profile at rank `r`. -/
noncomputable def matrixThetaC (r : ℕ) (t : ℝ) : ℂ := ((matrixTheta r t : ℝ) : ℂ)

/-- The matrix bank profile is locally integrable on the positive carrier axis: it is
antitone there. -/
lemma matrixThetaC_locallyIntegrableOn (r : ℕ) :
    LocallyIntegrableOn (matrixThetaC r) (Ioi (0 : ℝ)) volume := by
  rw [MeasureTheory.locallyIntegrableOn_iff isOpen_Ioi.isLocallyClosed]
  intro K hK hKc
  have hreal : IntegrableOn (matrixTheta r) K volume :=
    ((matrixTheta_antitoneOn r).mono hK).integrableOn_isCompact hKc
  exact hreal.ofReal

/-! ## The explicit tail bound -/

set_option maxHeartbeats 1000000 in
/-- The one-strand tail bound: above carrier height one,
`S(t) - 1 ≤ (2/(1 - e^{-π}))·e^{-πt}` — the off-DC phasors are dominated by a geometric
band starting at the first harmonic. -/
lemma strandTheta_sub_one_le {t : ℝ} (ht : 1 ≤ t) :
    strandTheta t - 1 ≤ 2 / (1 - Real.exp (-π)) * Real.exp (-π * t) := by
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht
  have hs : Summable fun n : ℤ => Real.exp (-π * t * (n : ℝ) ^ 2) :=
    summable_gaussInt ht0
  have hs1 : Summable fun n : ℕ => Real.exp (-π * t * (((n : ℤ) + 1 : ℤ) : ℝ) ^ 2) :=
    hs.comp_injective fun a b hab => by omega
  have hs2 : Summable fun n : ℕ => Real.exp (-π * t * ((-((n : ℤ) + 1) : ℤ) : ℝ) ^ 2) :=
    hs.comp_injective fun a b hab => by omega
  have hsplit := tsum_of_add_one_of_neg_add_one
    (f := fun n : ℤ => Real.exp (-π * t * (n : ℝ) ^ 2)) hs1 hs2
  have hneg_eq : (∑' n : ℕ, Real.exp (-π * t * ((-((n : ℤ) + 1) : ℤ) : ℝ) ^ 2)) =
      ∑' n : ℕ, Real.exp (-π * t * (((n : ℤ) + 1 : ℤ) : ℝ) ^ 2) := by
    refine tsum_congr fun n => ?_
    congr 1
    push_cast
    ring
  have hf0 : Real.exp (-π * t * (((0 : ℤ) : ℝ)) ^ 2) = 1 := by norm_num
  -- termwise geometric domination of the positive-harmonic band
  have hexp1 : Real.exp (-π) < 1 := by
    rw [Real.exp_lt_one_iff]
    nlinarith [Real.pi_pos]
  have hbound : ∀ n : ℕ, Real.exp (-π * t * (((n : ℤ) + 1 : ℤ) : ℝ) ^ 2) ≤
      Real.exp (-π * t) * Real.exp (-π) ^ n := by
    intro n
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have key : (0 : ℝ) ≤ (n : ℝ) * (t * (n : ℝ) + (2 * t - 1)) :=
      mul_nonneg hn (by nlinarith)
    push_cast
    nlinarith [mul_nonneg Real.pi_pos.le key]
  have hgeom : Summable fun n : ℕ => Real.exp (-π * t) * Real.exp (-π) ^ n :=
    (summable_geometric_of_lt_one (Real.exp_pos _).le hexp1).mul_left _
  have hA : (∑' n : ℕ, Real.exp (-π * t * (((n : ℤ) + 1 : ℤ) : ℝ) ^ 2)) ≤
      Real.exp (-π * t) * (1 - Real.exp (-π))⁻¹ := by
    calc (∑' n : ℕ, Real.exp (-π * t * (((n : ℤ) + 1 : ℤ) : ℝ) ^ 2))
        ≤ ∑' n : ℕ, Real.exp (-π * t) * Real.exp (-π) ^ n :=
          Summable.tsum_le_tsum hbound hs1 hgeom
      _ = Real.exp (-π * t) * (1 - Real.exp (-π))⁻¹ := by
          rw [tsum_mul_left, tsum_geometric_of_lt_one (Real.exp_pos _).le hexp1]
  have hst : strandTheta t =
      (∑' n : ℕ, Real.exp (-π * t * (((n : ℤ) + 1 : ℤ) : ℝ) ^ 2)) + 1 +
        ∑' n : ℕ, Real.exp (-π * t * (((n : ℤ) + 1 : ℤ) : ℝ) ^ 2) := by
    unfold strandTheta
    rw [hsplit, hneg_eq, hf0]
  have hpos : (0 : ℝ) < 1 - Real.exp (-π) := by linarith
  rw [hst]
  have h2 : 2 / (1 - Real.exp (-π)) * Real.exp (-π * t) =
      2 * (Real.exp (-π * t) * (1 - Real.exp (-π))⁻¹) := by
    field_simp
  rw [h2]
  linarith

/-- Telescoping power bound: for `1 ≤ S ≤ B`, `S^N - 1 ≤ N·B^{N-1}·(S - 1)` — the geometric
sum of `N` strand factors, each pinned below the height-one strand. -/
lemma pow_sub_one_le_of_le {S B : ℝ} (hS : 1 ≤ S) (hSB : S ≤ B) (N : ℕ) :
    S ^ N - 1 ≤ (N : ℝ) * B ^ (N - 1) * (S - 1) := by
  have h0S : (0 : ℝ) ≤ S := le_trans zero_le_one hS
  rw [← geom_sum_mul]
  apply mul_le_mul_of_nonneg_right _ (sub_nonneg.mpr hS)
  calc (∑ i ∈ Finset.range N, S ^ i) ≤ ∑ _i ∈ Finset.range N, B ^ (N - 1) := by
        refine Finset.sum_le_sum fun i hi => ?_
        calc S ^ i ≤ S ^ (N - 1) :=
              pow_le_pow_right₀ hS (by have := Finset.mem_range.mp hi; omega)
          _ ≤ B ^ (N - 1) := pow_le_pow_left₀ h0S hSB _
    _ = (N : ℝ) * B ^ (N - 1) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- The explicit rank-`r` tail constant:
`C_r = (r+1)²·S(1)^{(r+1)²-1}·2/(1 - e^{-π})`. -/
noncomputable def weldTailConst (r : ℕ) : ℝ :=
  (((r + 1) * (r + 1) : ℕ) : ℝ) * strandTheta 1 ^ ((r + 1) * (r + 1) - 1) *
    (2 / (1 - Real.exp (-π)))

/-- **The rank-`r` tail bound**: above carrier height one the matrix bank approaches its
DC mass `1` at the rate `e^{-πt}`, with the explicit constant `weldTailConst r`. -/
theorem matrixTheta_sub_one_le (r : ℕ) {t : ℝ} (ht : 1 ≤ t) :
    matrixTheta r t - 1 ≤ weldTailConst r * Real.exp (-π * t) := by
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht
  have hS1 : 1 ≤ strandTheta t := one_le_strandTheta ht0
  have hSB : strandTheta t ≤ strandTheta 1 := strandTheta_anti one_pos ht
  have hpow := pow_sub_one_le_of_le hS1 hSB ((r + 1) * (r + 1))
  have htail := strandTheta_sub_one_le ht
  have hc : (0 : ℝ) ≤ (((r + 1) * (r + 1) : ℕ) : ℝ) *
      strandTheta 1 ^ ((r + 1) * (r + 1) - 1) := by
    have hB : (0 : ℝ) ≤ strandTheta 1 := le_trans zero_le_one (one_le_strandTheta one_pos)
    positivity
  rw [matrixTheta_eq_pow r ht0]
  calc strandTheta t ^ ((r + 1) * (r + 1)) - 1
      ≤ (((r + 1) * (r + 1) : ℕ) : ℝ) * strandTheta 1 ^ ((r + 1) * (r + 1) - 1) *
          (strandTheta t - 1) := hpow
    _ ≤ (((r + 1) * (r + 1) : ℕ) : ℝ) * strandTheta 1 ^ ((r + 1) * (r + 1) - 1) *
          (2 / (1 - Real.exp (-π)) * Real.exp (-π * t)) :=
        mul_le_mul_of_nonneg_left htail hc
    _ = weldTailConst r * Real.exp (-π * t) := by
        unfold weldTailConst
        ring

/-! ## Superpolynomial decay at the top of the carrier -/

/-- The bank tail is dominated by every power at the top of the carrier:
`θ_r - 1 = O(t^p)` for every real `p` — the exponential tail beats every power. -/
lemma matrixThetaC_sub_one_isBigO (r : ℕ) (p : ℝ) :
    (fun t : ℝ => matrixThetaC r t - 1) =O[atTop] fun t : ℝ => t ^ p := by
  have hexp : (fun t : ℝ => Real.exp (-π * t)) =O[atTop] fun t : ℝ => t ^ p :=
    (isLittleO_exp_neg_mul_rpow_atTop Real.pi_pos p).isBigO
  refine IsBigO.trans ?_ hexp
  rw [Asymptotics.isBigO_iff]
  refine ⟨weldTailConst r, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht
  have h1 := one_le_matrixTheta r ht0
  have habs : ‖matrixThetaC r t - 1‖ = matrixTheta r t - 1 := by
    unfold matrixThetaC
    rw [show (1 : ℂ) = ((1 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  rw [habs, Real.norm_of_nonneg (Real.exp_pos _).le]
  exact matrixTheta_sub_one_le r ht

/-! ## The packaged weak functional-equation pair, at every rank -/

/-- **The rank-uniform weld pair.**  The matrix bank of rank `r`, packaged as a Mathlib
`WeakFEPair`: weight `(r+1)²/2`, root number `1`, both constant terms the DC mode `1`,
reflection from the compiled carrier-lattice weld `matrixTheta_inv`, decay from the
explicit tail bound.  Mathlib's abstract machinery then returns the entire part, both
poles with residues `±1`, and the completed functional equation — uniformly in the
rank.  Fiber-free: no cusp form, no automorphy, no L-function enters. -/
noncomputable def matrixWeldPair (r : ℕ) : WeakFEPair ℂ where
  f := matrixThetaC r
  g := matrixThetaC r
  k := (((r : ℝ) + 1) ^ 2) / 2
  ε := 1
  f₀ := 1
  g₀ := 1
  hf_int := matrixThetaC_locallyIntegrableOn r
  hg_int := matrixThetaC_locallyIntegrableOn r
  hk := by positivity
  hε := one_ne_zero
  h_feq := fun x hx => by
    have hx0 : (0 : ℝ) < x := hx
    unfold matrixThetaC
    rw [one_div, matrixTheta_inv r hx0]
    push_cast
    ring
  hf_top := fun p => matrixThetaC_sub_one_isBigO r p
  hg_top := fun p => matrixThetaC_sub_one_isBigO r p

/-! ## The continuation, poles, and functional equation — read off the pair -/

/-- The weight of the rank-`r` weld pair is `(r+1)²/2`. -/
@[simp] lemma matrixWeldPair_k (r : ℕ) :
    (matrixWeldPair r).k = (((r : ℝ) + 1) ^ 2) / 2 := rfl

/-- The root number of the rank-`r` weld pair is one. -/
@[simp] lemma matrixWeldPair_ε (r : ℕ) : (matrixWeldPair r).ε = 1 := rfl

/-- The constant term of the rank-`r` weld pair is the DC mode `1`. -/
@[simp] lemma matrixWeldPair_f₀ (r : ℕ) : (matrixWeldPair r).f₀ = 1 := rfl

/-- The dual constant term of the rank-`r` weld pair is the DC mode `1`. -/
@[simp] lemma matrixWeldPair_g₀ (r : ℕ) : (matrixWeldPair r).g₀ = 1 := rfl

/-- The entire part of the completed rank-`r` weld transform. -/
theorem matrixWeld_entirePart_differentiable (r : ℕ) :
    Differentiable ℂ (matrixWeldPair r).Λ₀ :=
  (matrixWeldPair r).differentiable_Λ₀

/-- **The completed functional equation at every rank**,
`Λ((r+1)²/2 - s) = Λ^∨(s)`: read off the packaged weld pair, uniformly in the rank. -/
theorem matrixWeld_functional_equation (r : ℕ) (s : ℂ) :
    (matrixWeldPair r).Λ ((((r : ℂ) + 1) ^ 2) / 2 - s) = (matrixWeldPair r).symm.Λ s := by
  have h := (matrixWeldPair r).functional_equation s
  rw [matrixWeldPair_k, matrixWeldPair_ε, one_smul] at h
  push_cast at h
  exact h

/-- **The pole at `s = (r+1)²/2` carries the DC mode**: the residue of the completed
rank-`r` weld transform at the weight is `+1`. -/
theorem matrixWeld_residue_k (r : ℕ) :
    Tendsto (fun s : ℂ => (s - (((r : ℂ) + 1) ^ 2) / 2) * (matrixWeldPair r).Λ s)
      (𝓝[≠] ((((r : ℂ) + 1) ^ 2) / 2)) (𝓝 1) := by
  have h := (matrixWeldPair r).Λ_residue_k
  rw [matrixWeldPair_k, matrixWeldPair_ε, matrixWeldPair_g₀, one_smul] at h
  have hcast : (((((r : ℝ) + 1) ^ 2) / 2 : ℝ) : ℂ) = (((r : ℂ) + 1) ^ 2) / 2 := by
    push_cast
    ring
  rw [hcast] at h
  simpa [smul_eq_mul] using h

/-- **The pole at `s = 0` carries the negative DC mode**: the residue of the completed
rank-`r` weld transform at the origin is `-1`. -/
theorem matrixWeld_residue_zero (r : ℕ) :
    Tendsto (fun s : ℂ => s * (matrixWeldPair r).Λ s) (𝓝[≠] 0) (𝓝 (-1)) := by
  have h := (matrixWeldPair r).Λ_residue_zero
  rw [matrixWeldPair_f₀] at h
  simpa [smul_eq_mul] using h

end CriticalLinePhasor.CarrierWeldPair

#print axioms CriticalLinePhasor.CarrierWeldPair.strandTheta_anti
#print axioms CriticalLinePhasor.CarrierWeldPair.matrixTheta_antitoneOn
#print axioms CriticalLinePhasor.CarrierWeldPair.matrixThetaC
#print axioms CriticalLinePhasor.CarrierWeldPair.matrixThetaC_locallyIntegrableOn
#print axioms CriticalLinePhasor.CarrierWeldPair.strandTheta_sub_one_le
#print axioms CriticalLinePhasor.CarrierWeldPair.pow_sub_one_le_of_le
#print axioms CriticalLinePhasor.CarrierWeldPair.weldTailConst
#print axioms CriticalLinePhasor.CarrierWeldPair.matrixTheta_sub_one_le
#print axioms CriticalLinePhasor.CarrierWeldPair.matrixThetaC_sub_one_isBigO
#print axioms CriticalLinePhasor.CarrierWeldPair.matrixWeldPair
#print axioms CriticalLinePhasor.CarrierWeldPair.matrixWeldPair_k
#print axioms CriticalLinePhasor.CarrierWeldPair.matrixWeldPair_ε
#print axioms CriticalLinePhasor.CarrierWeldPair.matrixWeldPair_f₀
#print axioms CriticalLinePhasor.CarrierWeldPair.matrixWeldPair_g₀
#print axioms CriticalLinePhasor.CarrierWeldPair.matrixWeld_entirePart_differentiable
#print axioms CriticalLinePhasor.CarrierWeldPair.matrixWeld_functional_equation
#print axioms CriticalLinePhasor.CarrierWeldPair.matrixWeld_residue_k
#print axioms CriticalLinePhasor.CarrierWeldPair.matrixWeld_residue_zero
