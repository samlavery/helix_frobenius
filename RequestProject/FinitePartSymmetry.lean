import Mathlib
import RequestProject.HadamardJets
import RequestProject.FoliatedGlobalPolarization
import RequestProject.HelixLedgerPairing
import RequestProject.DVPSeatRungOne

/-!
# The finite part of `ξ′/ξ` is odd under reflection, real under conjugation, and PURELY IMAGINARY on
# the line — at zeros included (ledger 593)

`xiFinitePart s = A + Σ'_ρ m_ρ (1/(s−ρ) + 1/ρ)` (584) equals `ξ′/ξ(s)` off the zeros and the finite part
of the Laurent expansion at a zero. The zero set is stable under `ρ ↦ 1 − ρ` (functional equation)
and `ρ ↦ ρ̄` (real coefficients), with the multiplicity invariant (`xiOrderNat_one_sub`,
`xiOrderNat_conj`). Reindexing the sum along these involutions:

* `xiFinitePart_one_sub`:  `FP(1 − s) = −FP(s)` for EVERY `s` (the constant `2A + Σ' m_ρ/(ρ(1−ρ))`
  vanishes, evaluated at `s = 2`);
* `xiHadamardConst_im`:    `A` is real (`ξ′/ξ(2)` is real: `ξ` commutes with conjugation);
* `xiFinitePart_conj`:     `FP(s̄) = conj FP(s)` for every `s`;
* **`re_xiFinitePart_of_re_half`**: `Re FP(s) = 0` for every `s` on the critical line.

On the line off the zeros this is `Re ξ′/ξ(½+it) = 0` (used in 587); AT a zero it is the reality of
the registered velocity field of the Newman flow (`ẋ_k = 2i·FP(ρ_k)`, ledger 570): every zero on the
line moves along the line. Chart-free: no convergence gate anywhere. Unconditional.
-/

open Complex Set Filter Topology

noncomputable section

namespace CriticalLinePhasor.ContourArgument

/-! ## 1. The two involutions of the zero set -/

theorem one_sub_mem_NontrivialZeros {ρ : ℂ} (hρ : ρ ∈ ZD.NontrivialZeros) :
    1 - ρ ∈ ZD.NontrivialZeros := by
  obtain ⟨h0, h1, hz⟩ := hρ
  refine ⟨by simp; linarith, by simp; linarith, ?_⟩
  have hn : ∀ n : ℕ, ρ ≠ -n := by
    intro n h
    have := congrArg Complex.re h
    simp at this
    linarith
  have h1' : ρ ≠ 1 := by
    intro h; rw [h] at h1; simp at h1
  rw [riemannZeta_one_sub hn h1', hz]
  simp

/-- `ρ ↦ 1 − ρ` on the zeros. -/
def mirrorZero : Zero ≃ Zero where
  toFun ρ := ⟨1 - ρ.val, one_sub_mem_NontrivialZeros ρ.2⟩
  invFun ρ := ⟨1 - ρ.val, one_sub_mem_NontrivialZeros ρ.2⟩
  left_inv ρ := by ext; simp
  right_inv ρ := by ext; simp

/-- `ρ ↦ ρ̄` on the zeros. -/
def conjZero : Zero ≃ Zero where
  toFun ρ := ⟨(starRingEnd ℂ) ρ.val, CriticalLinePhasor.DVP.conj_mem_NontrivialZeros ρ.2⟩
  invFun ρ := ⟨(starRingEnd ℂ) ρ.val, CriticalLinePhasor.DVP.conj_mem_NontrivialZeros ρ.2⟩
  left_inv ρ := by ext; simp
  right_inv ρ := by ext; simp

theorem mirrorZero_val (ρ : Zero) : (mirrorZero ρ).val = 1 - ρ.val := rfl
theorem conjZero_val (ρ : Zero) : (conjZero ρ).val = (starRingEnd ℂ) ρ.val := rfl

theorem xiOrderNat_mirrorZero (ρ : Zero) : ZD.xiOrderNat (mirrorZero ρ).val = ZD.xiOrderNat ρ.val := by
  rw [mirrorZero_val, CriticalLinePhasor.CaptureInterfaceAudit.xiOrderNat_one_sub]

theorem xiOrderNat_conjZero (ρ : Zero) : ZD.xiOrderNat (conjZero ρ).val = ZD.xiOrderNat ρ.val := by
  rw [conjZero_val, CriticalLinePhasor.FoliatedGlobalPolarization.xiOrderNat_conj]

/-! ## 2. Reflection: `FP(1 − s) = −FP(s)` -/

/-- The paired sum after reindexing by the mirror. -/
theorem hadamard_sum_one_sub (s : ℂ) :
    ∑' ρ : Zero, (ZD.xiOrderNat ρ.val : ℂ) * hadamardTerm ρ.val (1 - s)
      = ∑' ρ : Zero, (ZD.xiOrderNat ρ.val : ℂ) * (1 / (ρ.val - s) + 1 / (1 - ρ.val)) := by
  rw [← mirrorZero.tsum_eq]
  congr 1
  funext ρ
  rw [xiOrderNat_mirrorZero, mirrorZero_val]
  unfold hadamardTerm
  congr 2
  ring

/-- The pointwise identity behind the reflection: the `1/(ρ−s)` and `1/(s−ρ)` terms cancel. -/
theorem reflect_term_add (s ρ : ℂ) :
    (1 / (ρ - s) + 1 / (1 - ρ)) + (1 / (s - ρ) + 1 / ρ) = 1 / (1 - ρ) + 1 / ρ := by
  have : 1 / (ρ - s) + 1 / (s - ρ) = 0 := by
    rw [show s - ρ = -(ρ - s) by ring, div_neg]
    ring
  linear_combination this

theorem summable_reflect_family (s : ℂ) :
    Summable (fun ρ : Zero => (ZD.xiOrderNat ρ.val : ℂ) * (1 / (ρ.val - s) + 1 / (1 - ρ.val))) := by
  have h := (summable_hadamard_term_any (1 - s))
  rw [← mirrorZero.summable_iff] at h
  refine h.congr (fun ρ => ?_)
  simp only [Function.comp]
  rw [xiOrderNat_mirrorZero, mirrorZero_val]
  unfold hadamardTerm
  congr 2
  ring

/-- The reflection constant `2A + Σ' m_ρ (1/(1−ρ) + 1/ρ)`: `FP(1−s) + FP(s)` is this constant for every `s`. -/
theorem xiFinitePart_add_one_sub (s : ℂ) :
    xiFinitePart (1 - s) + xiFinitePart s
      = 2 * xiHadamardConst + ∑' ρ : Zero, (ZD.xiOrderNat ρ.val : ℂ) * (1 / (1 - ρ.val) + 1 / ρ.val) := by
  unfold xiFinitePart
  rw [hadamard_sum_one_sub]
  have h1 := summable_reflect_family s
  have h2 := summable_hadamard_term_any s
  have hsum : ∑' ρ : Zero, (ZD.xiOrderNat ρ.val : ℂ) * (1 / (ρ.val - s) + 1 / (1 - ρ.val))
      + ∑' ρ : Zero, (ZD.xiOrderNat ρ.val : ℂ) * hadamardTerm ρ.val s
      = ∑' ρ : Zero, (ZD.xiOrderNat ρ.val : ℂ) * (1 / (1 - ρ.val) + 1 / ρ.val) := by
    rw [← h1.tsum_add h2]
    congr 1
    funext ρ
    unfold hadamardTerm
    rw [← mul_add, reflect_term_add]
  linear_combination hsum

theorem two_ne_zero_mem : (2 : ℂ) ∉ ZD.NontrivialZeros := by
  intro h
  have := h.2.1
  norm_num at this

theorem neg_one_ne_zero_mem : (-1 : ℂ) ∉ ZD.NontrivialZeros := by
  intro h
  have := h.1
  norm_num at this

/-- The reflection constant vanishes. -/
theorem reflection_const_eq_zero :
    2 * xiHadamardConst + ∑' ρ : Zero, (ZD.xiOrderNat ρ.val : ℂ) * (1 / (1 - ρ.val) + 1 / ρ.val) = 0 := by
  have h := xiFinitePart_add_one_sub 2
  rw [show (1 : ℂ) - 2 = -1 by norm_num, xiFinitePart_eq_logDeriv neg_one_ne_zero_mem,
    xiFinitePart_eq_logDeriv two_ne_zero_mem] at h
  have hr := logDeriv_xi_reflect (2 : ℂ)
  rw [show (1 : ℂ) - 2 = -1 by norm_num] at hr
  rw [← h, hr]
  ring

/-- **`FP(1 − s) = −FP(s)` for every `s`.** -/
theorem xiFinitePart_one_sub (s : ℂ) : xiFinitePart (1 - s) = -xiFinitePart s := by
  have h := xiFinitePart_add_one_sub s
  rw [reflection_const_eq_zero] at h
  linear_combination h

/-! ## 3. Conjugation: `A` real and `FP(s̄) = conj FP(s)` -/

/-- A function commuting with conjugation has real derivative at real points. -/
theorem deriv_im_eq_zero_of_conj {f : ℂ → ℂ} (hf : ∀ z, f ((starRingEnd ℂ) z) = (starRingEnd ℂ) (f z))
    {x : ℝ} (hd : DifferentiableAt ℂ f x) : (deriv f x).im = 0 := by
  have hreal : ∀ y : ℝ, f y = ((f y).re : ℂ) := by
    intro y
    have h := hf y
    rw [Complex.conj_ofReal] at h
    exact (Complex.conj_eq_iff_re.mp h.symm).symm
  have h1 : HasDerivAt (fun y : ℝ => f y) (deriv f x) x := hd.hasDerivAt.comp_ofReal
  have h2 : HasDerivAt (fun y : ℝ => (f y).re) (deriv f x).re x := hd.hasDerivAt.real_of_complex
  have h3 : HasDerivAt (fun y : ℝ => ((f y).re : ℂ)) ((deriv f x).re : ℂ) x := h2.ofReal_comp
  have hfun : (fun y : ℝ => f y) = fun y : ℝ => ((f y).re : ℂ) := funext hreal
  rw [hfun] at h1
  have := h1.unique h3
  rw [this]
  simp

theorem logDeriv_xi_two_im : (logDeriv ZD.riemannXi 2).im = 0 := by
  rw [logDeriv_apply]
  have hξ : (ZD.riemannXi 2).im = 0 := by
    have h := riemannXi_conj 2
    rw [map_ofNat] at h
    exact Complex.conj_eq_iff_im.mp h.symm
  have hd : (deriv ZD.riemannXi 2).im = 0 :=
    deriv_im_eq_zero_of_conj riemannXi_conj (x := 2) (by
      simpa using (ZD.riemannXi_differentiable (2 : ℂ)))
  rw [Complex.div_im, hξ, hd]
  simp

/-- The Hadamard sum at `s = 2` is real (pair each zero with its conjugate). -/
theorem hadamard_sum_two_im :
    (∑' ρ : Zero, (ZD.xiOrderNat ρ.val : ℂ) * hadamardTerm ρ.val 2).im = 0 := by
  set S := ∑' ρ : Zero, (ZD.xiOrderNat ρ.val : ℂ) * hadamardTerm ρ.val 2 with hS
  have hconj : (starRingEnd ℂ) S = S := by
    rw [hS, ← Complex.conjCLE_apply, Complex.conjCLE.map_tsum, ← conjZero.tsum_eq]
    congr 1
    funext ρ
    rw [xiOrderNat_conjZero, conjZero_val, Complex.conjCLE_apply]
    unfold hadamardTerm
    simp only [map_mul, map_add, map_div₀, map_one, map_sub, Complex.conj_natCast, Complex.conj_conj,
      map_ofNat]
  exact Complex.conj_eq_iff_im.mp hconj

theorem xiHadamardConst_im : xiHadamardConst.im = 0 := by
  have h := xiHadamardConst_spec 2 two_ne_zero_mem
  have h2 : xiHadamardConst = deriv ZD.riemannXi 2 / ZD.riemannXi 2
      - ∑' ρ : Zero, (ZD.xiOrderNat ρ.val : ℂ) * hadamardTerm ρ.val 2 := by
    rw [h]; unfold hadamardTerm; ring
  rw [h2, Complex.sub_im, ← logDeriv_apply, logDeriv_xi_two_im, hadamard_sum_two_im]
  simp

/-- **`FP(s̄) = conj FP(s)` for every `s`.** -/
theorem xiFinitePart_conj (s : ℂ) :
    xiFinitePart ((starRingEnd ℂ) s) = (starRingEnd ℂ) (xiFinitePart s) := by
  unfold xiFinitePart
  rw [map_add]
  have hA : (starRingEnd ℂ) xiHadamardConst = xiHadamardConst :=
    Complex.conj_eq_iff_im.mpr xiHadamardConst_im
  rw [hA]
  congr 1
  conv_rhs => rw [← Complex.conjCLE_apply]
  rw [Complex.conjCLE.map_tsum, ← conjZero.tsum_eq]
  congr 1
  funext ρ
  rw [xiOrderNat_conjZero, conjZero_val, Complex.conjCLE_apply]
  unfold hadamardTerm
  simp only [map_mul, map_add, map_div₀, map_one, map_sub, Complex.conj_natCast]

/-! ## 4. On the line the finite part is purely imaginary — at zeros included -/

theorem conj_eq_one_sub_of_re_half' {s : ℂ} (h : s.re = 1 / 2) : (starRingEnd ℂ) s = 1 - s := by
  apply Complex.ext
  · simp [h]; norm_num
  · simp

/-- **`Re FP(s) = 0` on the critical line, for every `s` there** (off the zeros this is
`Re ξ′/ξ(½+it) = 0`; at a zero it is the reality of the registered velocity field). -/
theorem re_xiFinitePart_of_re_half {s : ℂ} (h : s.re = 1 / 2) : (xiFinitePart s).re = 0 := by
  have h1 := xiFinitePart_conj s
  rw [conj_eq_one_sub_of_re_half' h, xiFinitePart_one_sub] at h1
  -- −FP(s) = conj FP(s)
  have := congrArg Complex.re h1
  rw [Complex.neg_re, Complex.conj_re] at this
  linarith

/-- The velocity field of ledger 570, `ẋ_k = 2i·FP(ρ_k)`, is real at every zero on the line. -/
theorem velocity_real_of_re_half {ρ : ℂ} (h : ρ.re = 1 / 2) :
    (2 * I * xiFinitePart ρ).im = 0 := by
  have := re_xiFinitePart_of_re_half h
  simp [Complex.mul_im, this]

#print axioms one_sub_mem_NontrivialZeros
#print axioms xiFinitePart_one_sub
#print axioms xiFinitePart_conj
#print axioms re_xiFinitePart_of_re_half

end CriticalLinePhasor.ContourArgument
