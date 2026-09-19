import RequestProject.CarrierHamiltonian
import RequestProject.DVPCarrierContinuation

/-!
# The 3D zeta: the bank as the `H`-flow of the all-ones state, and the chart's zero as an event

`CarrierHamiltonian` proved the scalar statement `ζ(s) = Tr e^{−sH}`.  This file proves the
statement it is the shadow of.  The **3D zeta** is not a number but the *bank*
`B(s) := e^{−sH} 𝟙`, the vector of site phasors `x_n^{−s}`; the L-function is a **chart**
of it — a linear functional applied to the bank — and a zero of the chart is the 3D
**event** "the bank lies in the kernel of the chart".  Everything is unconditional.

* `bank_zero` : `B(0) = 𝟙` — every phasor at unit magnitude at height zero.
* `bank_flow` : `B(s + s') = e^{−s'H} B(s)` — **`H` generates the bank**; in `ℓ²`,
  `heat_bank`.
* `bank_line`, `norm_line_phase` : on the critical line `B(½ + it) = U(t) B(½)`, each phasor
  rotated by the unimodular `exp(−it·log x_n)` — **the 3D zeta on the line is a unitary orbit
  of one fixed state under the Stone group of `H`.**
* `bank_memℓp_iff` : **the critical line is the `ℓ²`-boundary of the bank**:
  `B(s) ∈ ℓ² ⟺ Re s > ½`.
* `chart_bank` : the plain chart `Σ_n` reads `ζ(s)` off the bank (`Re s > 1`);
  `LSeries_eq_chart_bank` : **every L-series is a chart of the same bank**, `L(s,f) = ⟨f, B(s)⟩`
  — the geometry `(H, B)` is shared, the L-function is the choice of chart.
* `laneChart_bank` : the paper's lane-balanced chart (phasors summed in pairs) reads the
  ordered readout `etaLim` (`DVPCarrierContinuation`), which is `(1 − 2^{1−s}) ζ(s)` on the
  whole channel `Re s > 0`.
* `zeta_zero_iff_bank_mem_ker` : **the chart's zero is the event `B(ρ) ∈ ker ℓ`**: in the
  strip, `ζ(s) = 0 ⟺ laneChart (B s) = 0`.

Read together: `H` generates the 3D zeta; the chart projects it to the 1D L-function; and the
chart's zero at `ρ` is the `H`-flow of `𝟙` entering the kernel of the chart at `ρ`.
-/

open scoped BigOperators ComplexConjugate LinearPMap LSeries.notation
open CarrierReadout

noncomputable section

namespace CarrierReadout

/-- **The 3D zeta**: the bank `B(s) = e^{−sH} 𝟙`, the vector of site phasors `x_n^{−s}`
(site `n+1` at index `n`). -/
def bank (s : ℂ) : ℕ → ℂ := fun n => ((n : ℂ) + 1) ^ (-s)

@[simp]
theorem bank_apply (s : ℂ) (n : ℕ) : bank s n = ((n : ℂ) + 1) ^ (-s) := rfl

/-- At height zero every phasor is at unit magnitude: `B(0) = 𝟙`. -/
theorem bank_zero : bank 0 = fun _ => (1 : ℂ) := by
  funext n; simp [bank]

/-- **`H` generates the bank**: `B(s + s') = e^{−s'H} B(s)`, componentwise. -/
theorem bank_flow (s s' : ℂ) (n : ℕ) :
    bank (s + s') n = ((n : ℂ) + 1) ^ (-s') * bank s n := by
  simp only [bank_apply]
  rw [heat_eigenvalue_add, mul_comm]

/-- **The bank on the critical line is a unitary orbit**: `B(½ + it) = U(t) B(½)`, with
`U(t) = e^{−itH}` rotating the `n`-th phasor by `exp(−it · log x_n)`. -/
theorem bank_line (t : ℝ) (n : ℕ) :
    bank (1 / 2 + Complex.I * t) n
      = Complex.exp (-(Complex.I * t) * (logWeight n : ℂ)) * bank (1 / 2) n := by
  rw [bank_flow, heat_eigenvalue_eq_exp]

/-- The rotation on the line is unimodular: `U(t)` is unitary phasor by phasor. -/
theorem norm_line_phase (t : ℝ) (n : ℕ) :
    ‖Complex.exp (-(Complex.I * t) * (logWeight n : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  simp [Complex.mul_re, Complex.mul_im]

/-! ### The critical line is the `ℓ²`-boundary of the bank -/

/-- The squared modulus of a phasor: `‖x_n^{−s}‖² = x_n^{−2 Re s}`. -/
theorem norm_bank_sq (s : ℂ) (n : ℕ) :
    ‖bank s n‖ ^ (2 : ℝ) = (((n + 1 : ℕ) : ℝ) ^ (2 * s.re))⁻¹ := by
  have hcast : ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) := by push_cast; ring
  have hpos : 0 < n + 1 := Nat.succ_pos n
  rw [bank_apply, hcast, Complex.norm_natCast_cpow_of_pos hpos, Complex.neg_re,
    ← Real.rpow_mul (by positivity), show -s.re * 2 = -(2 * s.re) by ring,
    Real.rpow_neg (by positivity)]

/-- **The critical line is the `ℓ²`-boundary of the bank**: `B(s) ∈ ℓ² ⟺ Re s > ½`. -/
theorem bank_memℓp_iff (s : ℂ) : Memℓp (bank s) 2 ↔ 1 / 2 < s.re := by
  rw [memℓp_gen_iff (by norm_num)]
  have h2 : ((2 : ENNReal).toReal) = (2 : ℝ) := by norm_num
  simp_rw [h2, norm_bank_sq]
  rw [summable_nat_add_iff (f := fun n : ℕ => (((n : ℝ)) ^ (2 * s.re))⁻¹) 1,
    Real.summable_nat_rpow_inv]
  constructor <;> intro h <;> linarith

/-- The flow stays in the Hilbert space: for `Re s > ½` and `Re s' ≥ 0`, `B(s)` lies in the
domain of `e^{−s'H}`. -/
theorem bank_mem_heatDomain {s s' : ℂ} (hs : 1 / 2 < s.re) (hs' : 0 ≤ s'.re) :
    (⟨bank s, (bank_memℓp_iff s).mpr hs⟩ : L2) ∈ (heat s').domain := by
  show Memℓp (fun n : ℕ => ((n : ℂ) + 1) ^ (-s') * bank s n) 2
  have hfun : (fun n : ℕ => ((n : ℂ) + 1) ^ (-s') * bank s n) = bank (s + s') := by
    funext n; rw [bank_flow]
  rw [hfun, bank_memℓp_iff, Complex.add_re]
  linarith

/-- **`H` generates the bank, in `ℓ²`**: `e^{−s'H}` carries `B(s)` to `B(s + s')`. -/
theorem heat_bank {s s' : ℂ} (hs : 1 / 2 < s.re) (hs' : 0 ≤ s'.re) :
    ((heat s' ⟨⟨bank s, (bank_memℓp_iff s).mpr hs⟩, bank_mem_heatDomain hs hs'⟩ : L2) : ℕ → ℂ)
      = bank (s + s') := by
  funext n
  rw [bank_flow]
  rfl

/-! ### Charts: the L-function as a linear reading of the bank -/

/-- The plain chart: the summation functional. -/
def chart (v : ℕ → ℂ) : ℂ := ∑' n, v n

/-- The plain chart reads `ζ` off the bank for `Re s > 1`. -/
theorem chart_bank {s : ℂ} (hs : 1 < s.re) : chart (bank s) = riemannZeta s := by
  unfold chart
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
  refine tsum_congr fun n => ?_
  rw [bank_apply, Complex.cpow_neg, one_div]

/-- **Universality of the bank**: every L-series is a chart of the same bank,
`L(s, f) = Σ_n f(x_n) · B(s)_n`.  The geometry `(H, B)` is shared; the L-function is the
choice of chart. -/
theorem LSeries_eq_chart_bank (f : ℕ → ℂ) {s : ℂ} (hf : LSeriesSummable f s) :
    LSeries f s = ∑' n, f (n + 1) * bank s n := by
  unfold LSeries
  rw [Summable.tsum_eq_zero_add hf, LSeries.term_zero, zero_add]
  refine tsum_congr fun n => ?_
  rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero n), bank_apply]
  push_cast
  rw [Complex.cpow_neg, div_eq_mul_inv]

/-- The paper's **lane-balanced chart** (Definition 11): the phasors summed in pairs, in the
order they enter. -/
def laneChart (v : ℕ → ℂ) : ℂ := ∑' k : ℕ, (v (2 * k) - v (2 * k + 1))

/-- The lane-balanced chart reads the ordered readout `etaLim` off the bank — for every `s`,
and `etaLim = (1 − 2^{1−s}) ζ` on the whole channel `Re s > 0`
(`CriticalLinePhasor.DVP.etaLim_eq_zeta`). -/
theorem laneChart_bank (s : ℂ) : laneChart (bank s) = CriticalLinePhasor.DVP.etaLim s := by
  unfold laneChart CriticalLinePhasor.DVP.etaLim
  refine tsum_congr fun k => ?_
  rw [CriticalLinePhasor.DVP.pairTerm_eq, bank_apply, bank_apply]
  push_cast
  ring_nf

/-- In the open strip the lane factor `1 − 2^{1−s}` does not vanish. -/
theorem lane_factor_ne_zero {s : ℂ} (hs1 : s.re < 1) : (1 - (2 : ℂ) ^ ((1 : ℂ) - s)) ≠ 0 := by
  intro h
  have h2 : (2 : ℂ) ^ ((1 : ℂ) - s) = 1 := by linear_combination -h
  have hn : ‖(2 : ℂ) ^ ((1 : ℂ) - s)‖ = 1 := by rw [h2, norm_one]
  have hcast : (2 : ℂ) = ((2 : ℕ) : ℂ) := by norm_num
  rw [hcast, Complex.norm_natCast_cpow_of_pos (by norm_num)] at hn
  have hlt : (1 : ℝ) < ((2 : ℕ) : ℝ) ^ (((1 : ℂ) - s).re) := by
    refine Real.one_lt_rpow (by norm_num) ?_
    simp [Complex.sub_re]
    linarith
  rw [hn] at hlt
  exact lt_irrefl _ hlt

/-- **The chart's zero is the 3D event `B(ρ) ∈ ker ℓ`.**  In the strip `0 < Re s < 1`,
`ζ(s) = 0` iff the lane-balanced chart annihilates the bank at `s`. -/
theorem zeta_zero_iff_bank_mem_ker {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    riemannZeta s = 0 ↔ laneChart (bank s) = 0 := by
  have hne1 : s ≠ 1 := by rintro rfl; norm_num at hs1
  rw [laneChart_bank, CriticalLinePhasor.DVP.etaLim_eq_zeta hs0 hne1]
  constructor
  · intro h; rw [h, mul_zero]
  · intro h; exact (mul_eq_zero.mp h).resolve_left (lane_factor_ne_zero hs1)

end CarrierReadout
