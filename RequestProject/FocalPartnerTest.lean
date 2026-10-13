import RequestProject.DriftFreeCompletion
import RequestProject.NativePencilSpectralSlot
import RequestProject.FocalQuotientFrobenius

/-!
# What the existing focal map does to the two same-height partner channels (ledger 1228)

Sam's test (2026-10-11): is the physical post-cancellation state a quotient/image of the two partner banks in
which the δ-independent cross-pairing descends to a positive self-pairing? Use the existing focal map and the
existing harmonic pencil; arbitrary `ρ`; input `ζ(ρ) = 0` / focal cancellation. The induced forms are DERIVED here,
not posited.

**The existing pencil** (`stageA`, `stageB`; arbitrary `s`).
* `reference_lane_kernel`: when the coupling vanishes, the post-cancellation kernel vector at the reference height
  `(N+1)/2` is the reference lane `e_ref`. It is the SAME vector, at the same real eigenvalue, for EVERY cancelling
  `s`; its metric mass is `N` (`stageB_reference`). So the pencil sends `ρ` and `ρ*` to one state, by forgetting `s`.
* `fiberMass_eq`: the fiber lane's metric mass is `Σ ‖w(n)‖² n^{−2 Re s}`.
* `fiberLane_partner_pairing`: the cross-pairing of the fiber lane at `ρ*` with the fiber lane at `ρ` is
  `Σ ‖w(n)‖² n^{−1}` for every `ρ` (the despin is unimodular). The pencil's metric `B` is block-diagonal with ONE
  fiber lane, so this cross-pairing is never formed by the pencil.
* `fiberMass_partner_iff`, `fiberMass_eq_crossPairing_iff`: the fiber lane's self-mass equals its partner's, or
  equals the cross-pairing, iff `Re ρ = ½`.

**The focal quotient** `Q` (configuration ↦ (mass, height)).
* `mass_phaseBlind`: the mass is unchanged by any per-site unit phases. Cancellation is a condition on phases, so
  `Q`'s induced norm cannot see it.
* `mass_smul`: under a scalar `u` the mass scales by `‖u‖`. A site dilation acts on the bank by `k^{−ρ}`, so it scales
  the post-cancellation mass by `k^{−σ}`. The phase `k^{−iγ}` is quotiented (`Q_rotate`).
* `partner_masses_dilate`: the partner masses scale by `k^{−σ}` and `k^{−(1−σ)}`; only their product has a
  `δ`-independent law (`k^{−1}`). With the area normalization `k^{½}` per state the product is invariant and each
  factor is boosted by `k^{∓δ}`: the dilation-invariant form on the pair is the hyperbolic `x·y`, not `x² + y²`.
* `focalMass_partner_iff`: the post-cancellation masses of the partner amplitude laws `n^{−σ}`, `n^{−(1−σ)}` (same
  routing, same head, same height) are equal iff `σ = ½`. By `Q_eq_iff`, `Q` identifies the partner channels iff
  `σ = ½`. (`Q` identifies the J-feet for every configuration: `Q_J`.)

**Where the partner pairing lives.** `site_partner_bilinear`, `partner_add`: per site, `n^{−ρ}·n^{−ρ*} =
n^{−(1 + 2iγ)}`, and `n^{−ρ}·conj(n^{−ρ*}) = n^{−1}` (`site_partner_product`). Both partner products are evaluations on
`Re = 1`, for every `ρ`. The cancellation is the evaluation at `ρ`.

The weighted comparison underlying all three iff statements is `weighted_power_sum_eq_iff`.
-/

open Complex Finset Matrix

noncomputable section

namespace CriticalLinePhasor.FocalPartner

open CriticalLinePhasor CriticalLinePhasor.SameHeight CriticalLinePhasor.DriftFreeCompletion
open CriticalLinePhasor.NativeSquare CriticalLinePhasor.Pencil3D CriticalLinePhasor.Geometric
open CriticalLinePhasor.SpectralFiber CriticalLinePhasor.FocalFeet CriticalLinePhasor.FocalQuotient
open CriticalLinePhasor.FocalEventProjection CriticalLinePhasor.ThreeDFocal
open CriticalLinePhasor.CarrierHeadFiniteFiber CriticalLinePhasor.GrownFiberEvolution
open CriticalLinePhasor.HarmonicCell

/-! ## 1. The weighted comparison -/

/-- **Weighted power sums at two exponents agree only at equal exponents.** -/
theorem weighted_power_sum_eq_iff {M : ℕ} {W : ℕ → ℝ} (hW : ∀ k ∈ Finset.range M, 0 ≤ W k)
    (hsite : ∃ k ∈ Finset.range M, 1 ≤ k ∧ 0 < W k) (a b : ℝ) :
    ∑ k ∈ Finset.range M, W k * ((k + 1 : ℕ) : ℝ) ^ (-a) =
      ∑ k ∈ Finset.range M, W k * ((k + 1 : ℕ) : ℝ) ^ (-b) ↔ a = b := by
  have key : ∀ a b : ℝ, a < b →
      ∑ k ∈ Finset.range M, W k * ((k + 1 : ℕ) : ℝ) ^ (-b) <
        ∑ k ∈ Finset.range M, W k * ((k + 1 : ℕ) : ℝ) ^ (-a) := by
    intro a b hab
    obtain ⟨k₀, hk₀, hk1, hWk⟩ := hsite
    refine Finset.sum_lt_sum (fun k hk => ?_) ⟨k₀, hk₀, ?_⟩
    · exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast Nat.le_add_left 1 k) (by linarith))
        (hW k hk)
    · exact mul_lt_mul_of_pos_left
        (Real.rpow_lt_rpow_of_exponent_lt (by exact_mod_cast (show 1 < k₀ + 1 by omega))
          (by linarith)) hWk
  constructor
  · intro h
    by_contra hab
    rcases lt_or_gt_of_ne hab with hlt | hlt
    · have := key a b hlt
      linarith
    · have := key b a hlt
      linarith
  · rintro rfl
    rfl

/-! ## 2. The existing pencil -/

/-- **The pencil's post-cancellation kernel vector is the reference lane, for every cancelling `s`.** -/
theorem reference_lane_kernel (w : ℕ → ℂ) (s : ℂ) (N : ℕ) (hc : nativeCoupling w s N = 0) :
    (stageA w s N - (((N : ℂ) + 1) / 2) • stageB w s N) *ᵥ
      (Pi.single (Sum.inl 0) 1 : Fin 1 ⊕ Fin 1 → ℂ) = 0 := by
  have hB21 : stageB w s N (Sum.inr 0) (Sum.inl 0) = 0 := by
    rw [stageB, twoLaneB_eq_blockDiag]
    simp
  funext i
  rw [Matrix.mulVec_single_one]
  rcases i with i | i
  · obtain rfl : i = 0 := Subsingleton.elim _ _
    rw [Matrix.col_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
      stageA_reference, stageB_reference, Pi.zero_apply]
    ring
  · obtain rfl : i = 0 := Subsingleton.elim _ _
    rw [Matrix.col_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
      stageA_coupling_adjoint, hc, hB21, star_zero, mul_zero, sub_zero, Pi.zero_apply]

/-- The fiber lane's metric mass. -/
theorem fiberMass_eq (w : ℕ → ℂ) {s : ℂ} (hs : s ≠ 0) (N : ℕ) :
    fiberMass w s N =
      ∑ k ∈ Finset.range N, ‖w (k + 1)‖ ^ 2 * ((k + 1 : ℕ) : ℝ) ^ (-(2 * s.re)) := by
  unfold fiberMass
  rw [← Fin.sum_univ_eq_sum_range
    (fun k => ‖w (k + 1)‖ ^ 2 * ((k + 1 : ℕ) : ℝ) ^ (-(2 * s.re))) N]
  refine Finset.sum_congr rfl fun k _ => ?_
  beta_reduce
  rw [readout_term_gen w hs, norm_mul, mul_pow,
    Complex.norm_natCast_cpow_of_pos (n := k.val + 1) (by omega),
    ← Real.rpow_mul_natCast (Nat.cast_nonneg _), Complex.neg_re]
  congr 2
  push_cast
  ring

/-- Per site, a bank and the conjugate of its partner multiply to `n^{−1}`. -/
theorem site_partner_product {n : ℕ} (hn : 1 ≤ n) (ρ : ℂ) :
    (n : ℂ) ^ (-ρ) * (starRingEnd ℂ) ((n : ℂ) ^ (-(partner ρ))) = ((n : ℝ)⁻¹ : ℂ) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hpow : (n : ℂ) ^ (-ρ) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]; tauto
  rw [bank_partner_inversion hn, map_div₀, Complex.conj_conj]
  have hconj1 : (starRingEnd ℂ) ((n : ℂ) ^ (-1 : ℂ)) = (n : ℂ)⁻¹ := by
    rw [Complex.cpow_neg_one, map_inv₀, Complex.conj_natCast]
  rw [hconj1]
  push_cast
  field_simp

/-- **The cross-pairing of the partner fiber lanes is `Σ ‖w(n)‖² n^{−1}`, for every `ρ`.** -/
theorem fiberLane_partner_pairing (w : ℕ → ℂ) {ρ : ℂ} (hρ : ρ ≠ 0) (hρ' : partner ρ ≠ 0) (N : ℕ) :
    ∑ k : Fin N, star (nativeFiberLane w (partner ρ) N k 0) * nativeFiberLane w ρ N k 0 =
      ∑ k : Fin N, ((‖w (k.val + 1)‖ ^ 2 * ((k.val + 1 : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) := by
  refine Finset.sum_congr rfl fun k _ => ?_
  have hcell : star ((cell (k.val + 1))⁻¹) * (cell (k.val + 1))⁻¹ = 1 := by
    rw [Complex.star_def, Complex.conj_mul', norm_inv, cell_norm, inv_one]
    simp
  have hsite := site_partner_product (Nat.le_add_left 1 k.val) ρ
  simp only [nativeFiberLane]
  rw [readout_term_gen w hρ, readout_term_gen w hρ']
  have hw : star (w (k.val + 1)) * w (k.val + 1) = ((‖w (k.val + 1)‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.conj_mul']
    push_cast
    rfl
  calc star ((cell (k.val + 1))⁻¹ * (w (k.val + 1) * ((k.val + 1 : ℕ) : ℂ) ^ (-(partner ρ)))) *
        ((cell (k.val + 1))⁻¹ * (w (k.val + 1) * ((k.val + 1 : ℕ) : ℂ) ^ (-ρ)))
      = (star ((cell (k.val + 1))⁻¹) * (cell (k.val + 1))⁻¹) *
          (star (w (k.val + 1)) * w (k.val + 1)) *
          (((k.val + 1 : ℕ) : ℂ) ^ (-ρ) *
            (starRingEnd ℂ) (((k.val + 1 : ℕ) : ℂ) ^ (-(partner ρ)))) := by
        rw [star_mul, star_mul, Complex.star_def]
        ring
    _ = _ := by
        rw [hcell, hw, hsite]
        push_cast
        ring

/-- **The fiber lane's self-mass equals its partner's iff `Re ρ = ½`.** -/
theorem fiberMass_partner_iff (w : ℕ → ℂ) (hw2 : w 2 ≠ 0) {N : ℕ} (hN : 2 ≤ N) {ρ : ℂ}
    (hρ : ρ ≠ 0) (hρ' : partner ρ ≠ 0) :
    fiberMass w ρ N = fiberMass w (partner ρ) N ↔ ρ.re = 1 / 2 := by
  rw [fiberMass_eq w hρ, fiberMass_eq w hρ', partner_re]
  have hsite : ∃ k ∈ Finset.range N, 1 ≤ k ∧ 0 < ‖w (k + 1)‖ ^ 2 :=
    ⟨1, Finset.mem_range.mpr (by omega), le_refl 1, by positivity⟩
  rw [weighted_power_sum_eq_iff (fun k _ => sq_nonneg _) hsite]
  constructor <;> intro h <;> linarith

/-- **The fiber lane's self-mass equals the partner cross-pairing iff `Re ρ = ½`.** -/
theorem fiberMass_eq_crossPairing_iff (w : ℕ → ℂ) (hw2 : w 2 ≠ 0) {N : ℕ} (hN : 2 ≤ N) {ρ : ℂ}
    (hρ : ρ ≠ 0) :
    fiberMass w ρ N =
        ∑ k ∈ Finset.range N, ‖w (k + 1)‖ ^ 2 * ((k + 1 : ℕ) : ℝ) ^ (-(1 : ℝ)) ↔
      ρ.re = 1 / 2 := by
  rw [fiberMass_eq w hρ]
  have hsite : ∃ k ∈ Finset.range N, 1 ≤ k ∧ 0 < ‖w (k + 1)‖ ^ 2 :=
    ⟨1, Finset.mem_range.mpr (by omega), le_refl 1, by positivity⟩
  rw [weighted_power_sum_eq_iff (fun k _ => sq_nonneg _) hsite]
  constructor <;> intro h <;> linarith

/-! ## 3. The focal quotient -/

/-- **`Q`'s mass is blind to per-site phases**, hence to cancellation. -/
theorem mass_phaseBlind (c : PhasorConfig) (u : Fin c.size → ℂ) (hu : ∀ k, ‖u k‖ = 1) :
    PhasorConfig.mass ⟨c.height, c.size, fun k => u k * c.phasor k⟩ = c.mass := by
  unfold PhasorConfig.mass
  simp [norm_mul, hu]

/-- Under a scalar the mass scales by its modulus. -/
theorem mass_smul (c : PhasorConfig) (u : ℂ) :
    PhasorConfig.mass ⟨c.height, c.size, fun k => u * c.phasor k⟩ = ‖u‖ * c.mass := by
  unfold PhasorConfig.mass
  simp [norm_mul, Finset.mul_sum]

/-- **Under the native site dilation the two partner masses move as a hyperbolic pair.** Each scales by the
modulus of its eigenvalue; only the PRODUCT has a law independent of `δ`, namely `k^{−1}`. -/
theorem partner_masses_dilate {k : ℕ} (hk : 1 ≤ k) (ρ : ℂ) (c c' : PhasorConfig) :
    PhasorConfig.mass ⟨c.height, c.size, fun j => (k : ℂ) ^ (-ρ) * c.phasor j⟩ *
        PhasorConfig.mass ⟨c'.height, c'.size, fun j => (k : ℂ) ^ (-(partner ρ)) * c'.phasor j⟩ =
      (k : ℝ)⁻¹ * (c.mass * c'.mass) := by
  rw [mass_smul, mass_smul, ← bank_partner_norm hk ρ]
  ring

/-- **The focal masses of the partner amplitude laws agree iff `σ = ½`.** Auxiliary (cleanup, ledger 1237):
the partner channels are not the conductor's banks, and this compares unsigned masses Σ|c|, not the two
mutually cancelling bank resultants. Not part of the canonical route. -/
theorem focalMass_partner_iff (w : ℕ → ℂ) (y σ : ℝ)
    (hsite : ∃ k ∈ Finset.range ⌈physicalHead y⌉₊,
      1 ≤ k ∧ 0 < headWindow (physicalHead y) k * ‖w (k + 1)‖) :
    headUnsigned w (fun k => ((k + 1 : ℕ) : ℝ) ^ (-σ)) y =
      headUnsigned w (fun k => ((k + 1 : ℕ) : ℝ) ^ (-(1 - σ))) y ↔ σ = 1 / 2 := by
  have key := weighted_power_sum_eq_iff (M := ⌈physicalHead y⌉₊)
    (W := fun k => headWindow (physicalHead y) k * ‖w (k + 1)‖)
    (fun k _ => mul_nonneg (smoothEntry_nonneg _) (norm_nonneg _)) hsite σ (1 - σ)
  unfold headUnsigned
  exact key.trans ⟨fun h => by linarith, fun h => by linarith⟩

/-! ## 4. Where the partner products live -/

theorem partner_add (ρ : ℂ) : ρ + partner ρ = 1 + 2 * I * (ρ.im : ℂ) := by
  apply Complex.ext <;> simp [partner] <;> ring

/-- **The bilinear partner product per site is an evaluation on `Re = 1`.** -/
theorem site_partner_bilinear {n : ℕ} (hn : 1 ≤ n) (ρ : ℂ) :
    (n : ℂ) ^ (-ρ) * (n : ℂ) ^ (-(partner ρ)) = (n : ℂ) ^ (-(1 + 2 * I * (ρ.im : ℂ))) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  rw [← Complex.cpow_add _ _ hn0, ← partner_add, neg_add]

end CriticalLinePhasor.FocalPartner

end

#print axioms CriticalLinePhasor.FocalPartner.weighted_power_sum_eq_iff
#print axioms CriticalLinePhasor.FocalPartner.reference_lane_kernel
#print axioms CriticalLinePhasor.FocalPartner.fiberMass_eq
#print axioms CriticalLinePhasor.FocalPartner.fiberLane_partner_pairing
#print axioms CriticalLinePhasor.FocalPartner.fiberMass_partner_iff
#print axioms CriticalLinePhasor.FocalPartner.fiberMass_eq_crossPairing_iff
#print axioms CriticalLinePhasor.FocalPartner.mass_phaseBlind
#print axioms CriticalLinePhasor.FocalPartner.mass_smul
#print axioms CriticalLinePhasor.FocalPartner.partner_masses_dilate
#print axioms CriticalLinePhasor.FocalPartner.focalMass_partner_iff
#print axioms CriticalLinePhasor.FocalPartner.site_partner_bilinear
