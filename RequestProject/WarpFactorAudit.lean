import RequestProject.FrobeniusFlowPencil
import RequestProject.CarrierRadialDegreeAudit

/-!
# The two factors of `e^{−sH}` against the native invariants (ledger 1197)

`eSH_split`: site by site, `(k+1)^{−s} = (k+1)^{−Re s} · mellinSpin (Im s) (k+1)`, i.e.
`e^{−sH} = D_{Re s} · U_{Im s}`. Here `U_t` is `FocalQuotient.frob t` (multiplication of site `k+1` by
`mellinSpin t (k+1)`, the first entry of `frobeniusBlock t (k+1)`) and `D_δ` is `dilate δ`
(multiplication of site `k+1` by the positive real `(k+1)^{−δ}`). They commute (`dilate_frob_comm`).

The invariants, factor by factor:

| invariant | `U_t` | `D_δ` (δ ≠ 0) |
|---|---|---|
| per-site amplitude | kept (`frob_phasor_norm`) | scaled by `(k+1)^{−δ}` (`dilate_phasor_norm`) |
| per-site direction | rotated | kept (`dilate_direction`) |
| unsigned mass `M` | kept (`frob_mass`) | changed (`dilate_testConfig_mass`) |
| house `J` | `J U_t = U_{−t} J` (`frob_J`) | `J D_δ = D_δ J` (`dilate_J`) |
| height label | kept; moves the event's spins `y ↦ y + t` (`frob_eventConfig_resultant`) | kept, spins unchanged |
| site-scale (no-drift) data | kept (`siteScaleProduct_add_imag`) | scaled by `(k+1)^{−δ}` (`siteScaleProduct_add_real`) |
| det of the per-site J-pair block | 1 (`frob_entry`, `frobeniusBlock_det_one`) | `(k+1)^{−2δ}` ≠ 1 (`dilate_block_det`, `dilate_block_det_ne_one`) |
| focal cancellation | not kept (`frob_not_focal_stable`) | not kept (`dilate_not_focal_stable`) |

Identification: `U_t` is the house height flow of the arclength generator up to a global unit phase
(`heightFlow_carrierLogWeight`: `heightFlow (carrierLogWeight Δ) t k = e^{−it log Δ} · mellinSpin t (k+1)`).
-/

open Complex

noncomputable section

namespace CriticalLinePhasor.WarpFactor

open CriticalLinePhasor CriticalLinePhasor.FocalEventProjection CriticalLinePhasor.CancellationEigenstatePair
open CriticalLinePhasor.FocalFeet CriticalLinePhasor.FocalFeet.PhasorConfig CriticalLinePhasor.FocalQuotient
open CriticalLinePhasor.FrobeniusFlow CriticalLinePhasor.GrownFiberEvolution

/-! ## The split -/

/-- **`e^{−sH} = D_{Re s} · U_{Im s}`, site by site.** -/
theorem eSH_split (s : ℂ) (k : ℕ) :
    ((k : ℂ) + 1) ^ (-s) =
      ((((k : ℝ) + 1) ^ (-s.re) : ℝ) : ℂ) * LFunctionPhasor.mellinSpin s.im (k + 1) := by
  have hx : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hc : ((k : ℂ) + 1) = (((k : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
  have hne : (((k : ℝ) + 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  rw [hc, show -s = (((-s.re : ℝ)) : ℂ) + (((-s.im : ℝ)) : ℂ) * I by
    apply Complex.ext <;> simp, Complex.cpow_add _ _ hne, ← Complex.ofReal_cpow hx.le]
  congr 1
  rw [Complex.cpow_def_of_ne_zero hne, ← Complex.ofReal_log hx.le]
  unfold LFunctionPhasor.mellinSpin
  congr 1
  push_cast
  ring

/-! ## `U_t`: the unimodular factor -/

theorem frob_phasor_norm (t : ℝ) (c : PhasorConfig) (k : Fin c.size) :
    ‖(frob t c).phasor k‖ = ‖c.phasor k‖ := by
  show ‖LFunctionPhasor.mellinSpin t ((k : ℕ) + 1) * c.phasor k‖ = _
  rw [norm_mul, LFunctionPhasor.mellinSpin_norm, one_mul]

/-- The site-scale (no-drift) data depend on `Re s` only. -/
theorem siteScaleProduct_add_imag (s : ℂ) (t : ℝ) (k : ℕ) :
    siteScaleProduct (s + (t : ℂ) * I) k = siteScaleProduct s k := by
  rw [siteScaleProduct_eq, siteScaleProduct_eq]
  simp

/-- **`U_t` is the house height flow of the arclength generator, up to a global unit phase.** -/
theorem heightFlow_carrierLogWeight {Δ : ℝ} (hΔ : 0 < Δ) (t : ℝ) (k : ℕ) :
    CarrierHelixGenerator.heightFlow (CarrierReadout.carrierLogWeight Δ) t k =
      Complex.exp (-((t * Real.log Δ : ℝ) : ℂ) * I) * LFunctionPhasor.mellinSpin t (k + 1) := by
  unfold CarrierHelixGenerator.heightFlow CarrierReadout.carrierLogWeight LFunctionPhasor.mellinSpin
  rw [Real.log_mul hΔ.ne' (by positivity), ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-! ## `D_δ`: the positive factor -/

/-- `D_δ`: site `k + 1` multiplied by `(k+1)^{−δ}`, at the same height. -/
def dilate (δ : ℝ) (c : PhasorConfig) : PhasorConfig :=
  ⟨c.height, c.size, fun k => ((((k : ℕ) : ℝ) + 1) ^ (-δ) : ℝ) * c.phasor k⟩

@[simp] theorem dilate_height (δ : ℝ) (c : PhasorConfig) : (dilate δ c).height = c.height := rfl

theorem dilate_phasor_norm (δ : ℝ) (c : PhasorConfig) (k : Fin c.size) :
    ‖(dilate δ c).phasor k‖ = (((k : ℕ) : ℝ) + 1) ^ (-δ) * ‖c.phasor k‖ := by
  show ‖((((k : ℕ) : ℝ) + 1) ^ (-δ) : ℝ) * c.phasor k‖ = _
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _)]

/-- `D_δ` keeps every phasor's direction. -/
theorem dilate_direction (δ : ℝ) (c : PhasorConfig) (k : Fin c.size) :
    Complex.arg ((dilate δ c).phasor k) = Complex.arg (c.phasor k) := by
  show Complex.arg (((((k : ℕ) : ℝ) + 1) ^ (-δ) : ℝ) * c.phasor k) = _
  exact Complex.arg_real_mul _ (Real.rpow_pos_of_pos (by positivity) _)

/-- **`D_δ` commutes with the house `J`.** -/
theorem dilate_J (δ : ℝ) (c : PhasorConfig) : dilate δ (PhasorConfig.J c) = PhasorConfig.J (dilate δ c) := by
  simp only [dilate, PhasorConfig.J, PhasorConfig.mk.injEq, true_and, heq_eq_eq]
  funext k
  rw [map_mul, Complex.conj_ofReal]

/-- The two factors commute. -/
theorem dilate_frob_comm (δ t : ℝ) (c : PhasorConfig) : dilate δ (frob t c) = frob t (dilate δ c) := by
  simp only [dilate, frob, PhasorConfig.mk.injEq, true_and, heq_eq_eq]
  funext k
  ring

/-- The determinant of `D_δ` on the per-site J-pair block. -/
theorem dilate_block_det (δ : ℝ) (k : ℕ) :
    Matrix.det !![((((k : ℝ) + 1) ^ (-δ) : ℝ) : ℂ), 0; 0, (starRingEnd ℂ) ((((k : ℝ) + 1) ^ (-δ) : ℝ) : ℂ)] =
      ((((k : ℝ) + 1) ^ (-(2 * δ)) : ℝ) : ℂ) := by
  have hpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  rw [Matrix.det_fin_two_of, mul_zero, sub_zero, Complex.conj_ofReal, ← Complex.ofReal_mul,
    ← Real.rpow_add hpos]
  congr 2
  ring

theorem dilate_block_det_ne_one {δ : ℝ} (hδ : δ ≠ 0) :
    Matrix.det !![((((1 : ℕ) : ℝ) + 1) ^ (-δ) : ℝ), 0; 0, ((((1 : ℕ) : ℝ) + 1) ^ (-δ) : ℝ)] ≠ (1 : ℝ) := by
  rw [Matrix.det_fin_two_of, mul_zero, sub_zero, ← Real.rpow_add (by norm_num)]
  intro h
  have h2 : Real.log ((((1 : ℕ) : ℝ) + 1) ^ (-δ + -δ)) = 0 := by rw [h, Real.log_one]
  rw [Real.log_rpow (by norm_num)] at h2
  have hl : Real.log (((1 : ℕ) : ℝ) + 1) ≠ 0 := by norm_num
  have := (mul_eq_zero.mp h2).resolve_right hl
  exact hδ (by linarith)

theorem two_rpow_ne_one {δ : ℝ} (hδ : δ ≠ 0) : (2 : ℝ) ^ (-δ) ≠ 1 := by
  intro h
  have h2 := congrArg Real.log h
  rw [Real.log_rpow (by norm_num), Real.log_one] at h2
  have hl : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  exact hδ (by have := (mul_eq_zero.mp h2).resolve_right hl; linarith)

/-- `D_δ` changes the unsigned mass. -/
theorem dilate_testConfig_mass {δ : ℝ} (hδ : δ ≠ 0) : (dilate δ testConfig).mass ≠ testConfig.mass := by
  rw [testConfig_mass]
  show ∑ k : Fin 2, ‖((((k : ℕ) : ℝ) + 1) ^ (-δ) : ℝ) * (![1, -1] : Fin 2 → ℂ) k‖ ≠ 2
  simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, norm_mul, Complex.norm_real, norm_neg, norm_one, mul_one]
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (by norm_num) _),
    Real.norm_of_nonneg (Real.rpow_nonneg (by norm_num) _)]
  norm_num
  intro h
  exact two_rpow_ne_one hδ (by linarith)

/-- `D_δ` does not keep focal cancellation. -/
theorem dilate_not_focal_stable {δ : ℝ} (hδ : δ ≠ 0) :
    testConfig.Cancels ∧ ¬ (dilate δ testConfig).Cancels := by
  refine ⟨testConfig_cancels, ?_⟩
  unfold PhasorConfig.Cancels PhasorConfig.resultant
  show ¬ ∑ k : Fin 2, ((((k : ℕ) : ℝ) + 1) ^ (-δ) : ℝ) * (![1, -1] : Fin 2 → ℂ) k = 0
  rw [Fin.sum_univ_two]
  intro h
  apply two_rpow_ne_one hδ
  have hre := congrArg Complex.re h
  simp only [Fin.val_zero, Fin.val_one, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.one_re, Complex.one_im, Complex.neg_re, Complex.neg_im, Complex.zero_re] at hre
  norm_num at hre
  linarith

end CriticalLinePhasor.WarpFactor

#print axioms CriticalLinePhasor.WarpFactor.eSH_split
#print axioms CriticalLinePhasor.WarpFactor.frob_phasor_norm
#print axioms CriticalLinePhasor.WarpFactor.siteScaleProduct_add_imag
#print axioms CriticalLinePhasor.WarpFactor.heightFlow_carrierLogWeight
#print axioms CriticalLinePhasor.WarpFactor.dilate_phasor_norm
#print axioms CriticalLinePhasor.WarpFactor.dilate_direction
#print axioms CriticalLinePhasor.WarpFactor.dilate_J
#print axioms CriticalLinePhasor.WarpFactor.dilate_frob_comm
#print axioms CriticalLinePhasor.WarpFactor.dilate_block_det
#print axioms CriticalLinePhasor.WarpFactor.dilate_block_det_ne_one
#print axioms CriticalLinePhasor.WarpFactor.dilate_testConfig_mass
#print axioms CriticalLinePhasor.WarpFactor.dilate_not_focal_stable
