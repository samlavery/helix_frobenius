import Mathlib
import RequestProject.SeatScalarCriterion
import RequestProject.FoliatedGlobalPolarization

/-!
# The seat at prime-computable anchors: order-`n` detection outside the strip (ledger 544)

The scalar seat energy `Σ_ρ m_ρ (t_ρ−w)⁻¹(t_ρ−w̄)⁻¹` is nonnegative unconditionally at every
anchor outside the strip (`seat_energy_nonneg_of_outside_strip`), and its converse needs anchors
inside the strip (`exists_seat_energy_neg`).  This file moves the detection OUTSIDE the strip by
raising the order: with resolvent nodes `u_ρ = (t_ρ−w)⁻¹`, `u'_ρ = (t_ρ−w̄)⁻¹`, the order-`n`
FE-paired form is

  `Q_w(v) = Σ_ρ m_ρ · (Σ_j conj v_j u_ρ^{j+1}) · (Σ_k v_k u'_ρ^{k+1})`,

whose entries `Σ_ρ m_ρ u_ρ^{j+1} u'_ρ^{k+1}` are finite partial-fraction combinations of jets of
`ξ′/ξ` at the chart points `s = ½+iw` and `1−s̄`: for `Re s > 1` they are absolutely convergent
Dirichlet series.  Main theorem (`exists_primeAnchor_form_neg`): an off-line zero forces an anchor
with `1 < Re s < 3/2`, at the ordinate of a locally extremal off-line zero `ρ*`, and a test
polynomial `R(x) = x^N (x − m₀)` with `Q_w(v_R) < 0`.  Mechanism: at that anchor the pair
`{ρ*, 1−ρ̄*}` has node product `ab = 1/((σ₀−½)² − y²)` while every other zero has node product
`≤ K < ab`, so the pair's cross term `2 m R(a) R(b) < 0` dominates geometrically in `N`.

Together with the on-line direction (`primeAnchorForm_re_nonneg_of_online`) this is the seat
relocated to the prime-computable bank: RH ⟺ the order-`n` FE-paired form is nonnegative at every
anchor with `1 < Re s < 3/2` and every `n`.  No `sorry`, no `axiom`.
-/

open Complex Filter Topology
open CriticalLinePhasor.HilbertPolya
open CriticalLinePhasor.FoliatedGlobalPolarization
open CriticalLinePhasor.FoliatedPolarization (feReflect)

noncomputable section

namespace CriticalLinePhasor.SeatPrimeAnchor

/-- The resolvent node at the anchor. -/
def node (w : ℂ) (ρ : Zero) : ℂ := (spectralCoord ρ.val - w)⁻¹

/-- The FE-conjugate resolvent node. -/
def node' (w : ℂ) (ρ : Zero) : ℂ := (spectralCoord ρ.val - (starRingEnd ℂ) w)⁻¹

/-- The real test polynomial `R(x) = x^N (x − m₀)`, evaluated on `ℂ`. -/
def Rf (N : ℕ) (m₀ : ℝ) (x : ℂ) : ℂ := x ^ N * (x - m₀)

/-- The `ρ`-term of the order-`(N+2)` FE-paired form along the test polynomial `R`, in the
`i`-twisted coordinates `x = i u`, `x' = −i u'` that make the pair terms real. -/
def primeAnchorTerm (w : ℂ) (N : ℕ) (m₀ : ℝ) (ρ : Zero) : ℂ :=
  (ZD.xiOrderNat ρ.val : ℂ) * (Rf N m₀ (I * node w ρ) * Rf N m₀ (-I * node' w ρ))

/-- The order-`(N+2)` FE-paired form along `R`. -/
def primeAnchorForm (w : ℂ) (N : ℕ) (m₀ : ℝ) : ℂ := ∑' ρ : Zero, primeAnchorTerm w N m₀ ρ

/-! ## Chart facts -/

theorem chart_eq (γ σ₀ : ℝ) :
    (1 / 2 : ℂ) + I * ((γ : ℂ) + ((1 / 2 - σ₀ : ℝ) : ℂ) * I) = (σ₀ : ℂ) + (γ : ℂ) * I := by
  push_cast
  linear_combination ((1 / 2 : ℂ) - σ₀) * I_sq

theorem node_norm (w : ℂ) (ρ : Zero) : ‖node w ρ‖ = ‖(1 / 2 + I * w) - ρ.val‖⁻¹ := by
  unfold node
  rw [norm_inv, CriticalLinePhasor.SeatScalar.norm_spectralCoord_sub]

theorem node'_norm (w : ℂ) (ρ : Zero) :
    ‖node' w ρ‖ = ‖(1 / 2 + I * (starRingEnd ℂ) w) - ρ.val‖⁻¹ := by
  unfold node'
  rw [norm_inv, CriticalLinePhasor.SeatScalar.norm_spectralCoord_sub]

/-- `‖Rf N m₀ x‖ ≤ ‖x‖^N (‖x‖ + |m₀|)`. -/
theorem Rf_norm_le (N : ℕ) (m₀ : ℝ) (x : ℂ) : ‖Rf N m₀ x‖ ≤ ‖x‖ ^ N * (‖x‖ + |m₀|) := by
  unfold Rf
  rw [norm_mul, norm_pow]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc ‖x - (m₀ : ℂ)‖ ≤ ‖x‖ + ‖(m₀ : ℂ)‖ := norm_sub_le _ _
    _ = ‖x‖ + |m₀| := by rw [Complex.norm_real, Real.norm_eq_abs]

/-! ## The on-line direction -/

/-- For an on-line zero the two twisted nodes are conjugate: `−i u' = conj (i u)`. -/
theorem twisted_nodes_conj_of_online {w : ℂ} {ρ : Zero} (hρ : ρ.val.re = 1 / 2) :
    -I * node' w ρ = (starRingEnd ℂ) (I * node w ρ) := by
  unfold node node'
  have ht : (starRingEnd ℂ) (spectralCoord ρ.val) = spectralCoord ρ.val := by
    rw [Complex.conj_eq_iff_im]
    unfold spectralCoord
    simp [hρ]
  rw [map_mul, Complex.conj_I, map_inv₀, map_sub, ht]

/-- `Rf` commutes with conjugation (real coefficients). -/
theorem Rf_conj (N : ℕ) (m₀ : ℝ) (x : ℂ) :
    Rf N m₀ ((starRingEnd ℂ) x) = (starRingEnd ℂ) (Rf N m₀ x) := by
  unfold Rf
  rw [map_mul, map_pow, map_sub, Complex.conj_ofReal]

/-- On the line every term is `m_ρ |Rf(i u_ρ)|² ≥ 0`. -/
theorem primeAnchorTerm_re_nonneg_of_online {w : ℂ} (N : ℕ) (m₀ : ℝ) {ρ : Zero}
    (hρ : ρ.val.re = 1 / 2) : 0 ≤ (primeAnchorTerm w N m₀ ρ).re ∧
      (primeAnchorTerm w N m₀ ρ).im = 0 := by
  unfold primeAnchorTerm
  rw [twisted_nodes_conj_of_online hρ, Rf_conj, Complex.mul_conj, ← Complex.ofReal_natCast,
    ← Complex.ofReal_mul]
  constructor
  · rw [Complex.ofReal_re]
    exact mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _)
  · rw [Complex.ofReal_im]

/-- **The on-line direction**: if every zero is on the line, the form is real and nonnegative at
every anchor (given summability). -/
theorem primeAnchorForm_re_nonneg_of_online {w : ℂ} (N : ℕ) (m₀ : ℝ)
    (hon : ∀ ρ ∈ ZD.NontrivialZeros, ρ.re = 1 / 2)
    (hsum : Summable (primeAnchorTerm w N m₀)) :
    0 ≤ (primeAnchorForm w N m₀).re := by
  unfold primeAnchorForm
  rw [Complex.re_tsum hsum]
  exact tsum_nonneg (fun ρ => (primeAnchorTerm_re_nonneg_of_online N m₀ (hon ρ.val ρ.2)).1)

/-! ## The pair at a locally extremal off-line zero -/

/-- The anchor over the ordinate `γ` with chart abscissa `σ₀`. -/
def anchor (γ σ₀ : ℝ) : ℂ := (γ : ℂ) + ((1 / 2 - σ₀ : ℝ) : ℂ) * I

theorem anchor_conj (γ σ₀ : ℝ) :
    (starRingEnd ℂ) (anchor γ σ₀) = (γ : ℂ) - ((1 / 2 - σ₀ : ℝ) : ℂ) * I := by
  unfold anchor
  rw [map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]
  ring

/-- `t_ρ − w` at the anchor over `ρ`'s own ordinate: `i(σ₀ − Re ρ)`. -/
theorem spectralCoord_sub_anchor (ρ : ℂ) (σ₀ : ℝ) :
    spectralCoord ρ - anchor ρ.im σ₀ = I * ((σ₀ : ℂ) - ρ.re) := by
  unfold spectralCoord anchor
  apply Complex.ext <;> simp

/-- `t_ρ − w̄` at the anchor over `ρ`'s own ordinate: `−i(σ₀ − 1 + Re ρ)`. -/
theorem spectralCoord_sub_anchor_conj (ρ : ℂ) (σ₀ : ℝ) :
    spectralCoord ρ - (starRingEnd ℂ) (anchor ρ.im σ₀) = -I * ((σ₀ : ℂ) - 1 + ρ.re) := by
  rw [anchor_conj]
  unfold spectralCoord
  apply Complex.ext <;> simp
  ring

theorem neg_I_inv : (-I)⁻¹ = I := by
  rw [inv_neg, Complex.inv_I, neg_neg]

theorem neg_I_mul_I : -I * I = (1 : ℂ) := by
  rw [neg_mul, I_mul_I, neg_neg]

/-- The twisted node of `ρ*` at its own anchor is the real number `a = 1/(σ₀ − β*)`. -/
theorem twisted_node_self (ρ : Zero) (σ₀ : ℝ) :
    I * node (anchor ρ.val.im σ₀) ρ = ((σ₀ - ρ.val.re)⁻¹ : ℝ) := by
  unfold node
  rw [spectralCoord_sub_anchor, mul_inv, ← mul_assoc, mul_inv_cancel₀ I_ne_zero, one_mul]
  push_cast
  rfl

/-- The twisted conjugate node of `ρ*` at its own anchor is the real number `b = 1/(σ₀−1+β*)`. -/
theorem twisted_node'_self (ρ : Zero) (σ₀ : ℝ) :
    -I * node' (anchor ρ.val.im σ₀) ρ = ((σ₀ - 1 + ρ.val.re)⁻¹ : ℝ) := by
  unfold node'
  rw [spectralCoord_sub_anchor_conj, mul_inv, neg_I_inv, ← mul_assoc, neg_I_mul_I, one_mul]
  push_cast
  rfl

theorem feReflect_im (ρ : ℂ) : (feReflect ρ).im = ρ.im := by
  simp [feReflect, Complex.sub_im, Complex.conj_im]

theorem feReflect_re (ρ : ℂ) : (feReflect ρ).re = 1 - ρ.re := by
  simp [feReflect, Complex.sub_re, Complex.conj_re]

/-- The FE partner `ρ' = 1 − ρ̄*` has spectral coordinate `conj t*`; at the anchor over the
common ordinate its twisted nodes are `b` and `a` (swapped). -/
theorem twisted_node_partner (ρ : Zero) (σ₀ : ℝ) :
    I * node (anchor ρ.val.im σ₀) (feReflectZ ρ) = ((σ₀ - 1 + ρ.val.re)⁻¹ : ℝ) := by
  unfold node
  rw [feReflectZ_val]
  have key : spectralCoord (feReflect ρ.val) - anchor ρ.val.im σ₀
      = I * ((σ₀ : ℂ) - 1 + ρ.val.re) := by
    have h1 := spectralCoord_sub_anchor (feReflect ρ.val) σ₀
    rw [feReflect_im, feReflect_re] at h1
    rw [h1]
    push_cast
    ring
  rw [key, mul_inv, ← mul_assoc, mul_inv_cancel₀ I_ne_zero, one_mul]
  push_cast
  rfl

theorem twisted_node'_partner (ρ : Zero) (σ₀ : ℝ) :
    -I * node' (anchor ρ.val.im σ₀) (feReflectZ ρ) = ((σ₀ - ρ.val.re)⁻¹ : ℝ) := by
  unfold node'
  rw [feReflectZ_val]
  have key : spectralCoord (feReflect ρ.val) - (starRingEnd ℂ) (anchor ρ.val.im σ₀)
      = -I * ((σ₀ : ℂ) - ρ.val.re) := by
    have h1 := spectralCoord_sub_anchor_conj (feReflect ρ.val) σ₀
    rw [feReflect_im, feReflect_re] at h1
    rw [h1]
    push_cast
    ring
  rw [key, mul_inv, neg_I_inv, ← mul_assoc, neg_I_mul_I, one_mul]
  push_cast
  rfl

/-- **The pair's contribution is real and equals `2 m R(a) R(b)`.** -/
theorem pair_terms (ρ : Zero) (σ₀ : ℝ) (N : ℕ) (m₀ : ℝ) :
    primeAnchorTerm (anchor ρ.val.im σ₀) N m₀ ρ
      + primeAnchorTerm (anchor ρ.val.im σ₀) N m₀ (feReflectZ ρ)
      = ((2 * (ZD.xiOrderNat ρ.val : ℝ)
          * ((σ₀ - ρ.val.re)⁻¹ ^ N * ((σ₀ - ρ.val.re)⁻¹ - m₀))
          * ((σ₀ - 1 + ρ.val.re)⁻¹ ^ N * ((σ₀ - 1 + ρ.val.re)⁻¹ - m₀)) : ℝ) : ℂ) := by
  unfold primeAnchorTerm
  rw [twisted_node_self ρ σ₀, twisted_node'_self ρ σ₀, twisted_node_partner ρ σ₀,
    twisted_node'_partner ρ σ₀, feReflectZ_val, xiOrderNat_feReflect]
  unfold Rf
  push_cast
  ring

/-! ## Summability at anchors outside the strip -/

/-- The chart point of the anchor is `σ₀ + iγ`. -/
theorem chart_anchor (γ σ₀ : ℝ) : (1 / 2 : ℂ) + I * anchor γ σ₀ = (σ₀ : ℂ) + (γ : ℂ) * I := by
  unfold anchor
  exact chart_eq γ σ₀

/-- The conjugate chart point of the anchor is `(1 − σ₀) + iγ`. -/
theorem chart_anchor_conj (γ σ₀ : ℝ) :
    (1 / 2 : ℂ) + I * (starRingEnd ℂ) (anchor γ σ₀) = ((1 - σ₀ : ℝ) : ℂ) + (γ : ℂ) * I := by
  rw [anchor_conj]
  push_cast
  linear_combination (-(1 / 2 : ℂ) + σ₀) * I_sq

theorem chart_anchor_not_zero {γ σ₀ : ℝ} (h : 1 < σ₀) :
    ((1 / 2 : ℂ) + I * anchor γ σ₀) ∉ ZD.NontrivialZeros := by
  rw [chart_anchor]
  intro hz
  obtain ⟨-, h2, -⟩ := hz
  simp at h2
  linarith

theorem chart_anchor_conj_not_zero {γ σ₀ : ℝ} (h : 1 < σ₀) :
    ((1 / 2 : ℂ) + I * (starRingEnd ℂ) (anchor γ σ₀)) ∉ ZD.NontrivialZeros := by
  rw [chart_anchor_conj]
  intro hz
  obtain ⟨h1, -, -⟩ := hz
  simp at h1
  linarith

theorem anchor_sub_conj_ne {γ σ₀ : ℝ} (h : 1 < σ₀) :
    anchor γ σ₀ - (starRingEnd ℂ) (anchor γ σ₀) ≠ 0 := by
  rw [anchor_conj]
  unfold anchor
  intro h0
  have := congrArg Complex.im h0
  simp at this
  linarith

/-- The seat-energy term's norm is `m_ρ ‖u_ρ‖ ‖u'_ρ‖`. -/
theorem seat_term_norm (w : ℂ) (ρ : Zero) :
    ‖(ZD.xiOrderNat ρ.val : ℂ) * ((spectralCoord ρ.val - w)⁻¹ *
        (spectralCoord ρ.val - (starRingEnd ℂ) w)⁻¹)‖
      = (ZD.xiOrderNat ρ.val : ℝ) * (‖node w ρ‖ * ‖node' w ρ‖) := by
  unfold node node'
  rw [norm_mul, norm_mul, Complex.norm_natCast]

/-- The node-product weights `m_ρ ‖u_ρ‖ ‖u'_ρ‖` are summable at an anchor outside the strip. -/
theorem summable_node_product {γ σ₀ : ℝ} (h : 1 < σ₀) :
    Summable (fun ρ : Zero =>
      (ZD.xiOrderNat ρ.val : ℝ) * (‖node (anchor γ σ₀) ρ‖ * ‖node' (anchor γ σ₀) ρ‖)) := by
  have hs := CriticalLinePhasor.SeatScalar.summable_seat_energy
    (chart_anchor_not_zero (γ := γ) h) (chart_anchor_conj_not_zero (γ := γ) h)
    (anchor_sub_conj_ne (γ := γ) h)
  have hn := summable_norm_iff.mpr hs
  refine hn.congr (fun ρ => ?_)
  exact seat_term_norm _ ρ

/-- Node bounds outside the strip: `‖u_ρ‖ ≤ 1/(σ₀−1)` and `‖u'_ρ‖ ≤ 1/(σ₀−1)`. -/
theorem node_le {γ σ₀ : ℝ} (h : 1 < σ₀) (ρ : Zero) : ‖node (anchor γ σ₀) ρ‖ ≤ (σ₀ - 1)⁻¹ := by
  rw [node_norm, chart_anchor]
  apply inv_anti₀ (by linarith)
  have hre : |((σ₀ : ℂ) + (γ : ℂ) * I - ρ.val).re| ≤ ‖(σ₀ : ℂ) + (γ : ℂ) * I - ρ.val‖ :=
    Complex.abs_re_le_norm _
  have hre' : ((σ₀ : ℂ) + (γ : ℂ) * I - ρ.val).re = σ₀ - ρ.val.re := by simp
  rw [hre'] at hre
  have hρ1 : ρ.val.re < 1 := ρ.2.2.1
  calc σ₀ - 1 ≤ σ₀ - ρ.val.re := by linarith
    _ ≤ |σ₀ - ρ.val.re| := le_abs_self _
    _ ≤ _ := hre

theorem node'_le {γ σ₀ : ℝ} (h : 1 < σ₀) (ρ : Zero) : ‖node' (anchor γ σ₀) ρ‖ ≤ (σ₀ - 1)⁻¹ := by
  rw [node'_norm, chart_anchor_conj]
  apply inv_anti₀ (by linarith)
  have hre : |(((1 - σ₀ : ℝ) : ℂ) + (γ : ℂ) * I - ρ.val).re|
      ≤ ‖((1 - σ₀ : ℝ) : ℂ) + (γ : ℂ) * I - ρ.val‖ := Complex.abs_re_le_norm _
  have hre' : (((1 - σ₀ : ℝ) : ℂ) + (γ : ℂ) * I - ρ.val).re = 1 - σ₀ - ρ.val.re := by simp
  rw [hre'] at hre
  have hρ0 : 0 < ρ.val.re := ρ.2.1
  calc σ₀ - 1 ≤ σ₀ - 1 + ρ.val.re := by linarith
    _ = |1 - σ₀ - ρ.val.re| := by rw [abs_of_neg (by linarith)]; ring
    _ ≤ _ := hre

/-- **Summability of the order-`n` form** at an anchor outside the strip (`N ≥ 1`: the test
polynomial has no constant term, so the terms decay like the seat energy's). -/
theorem summable_primeAnchorTerm {γ σ₀ : ℝ} (h : 1 < σ₀) {N : ℕ} (hN : 1 ≤ N) (m₀ : ℝ) :
    Summable (primeAnchorTerm (anchor γ σ₀) N m₀) := by
  set U : ℝ := (σ₀ - 1)⁻¹ with hU
  have hU0 : 0 ≤ U := by rw [hU]; positivity
  set C : ℝ := (U ^ (N - 1) * (U + |m₀|)) * (U ^ (N - 1) * (U + |m₀|)) with hC
  have hmaj := (summable_node_product (γ := γ) h).mul_left C
  refine Summable.of_norm_bounded hmaj (fun ρ => ?_)
  unfold primeAnchorTerm
  rw [norm_mul, norm_mul, Complex.norm_natCast]
  have hu := node_le (γ := γ) h ρ
  have hu' := node'_le (γ := γ) h ρ
  have hf : ∀ x : ℂ, ‖x‖ ≤ U → ‖Rf N m₀ x‖ ≤ ‖x‖ * (U ^ (N - 1) * (U + |m₀|)) := by
    intro x hx
    have h1 := Rf_norm_le N m₀ x
    have hx0 : 0 ≤ ‖x‖ := norm_nonneg _
    have hpow : ‖x‖ ^ N ≤ ‖x‖ * U ^ (N - 1) := by
      obtain ⟨k, hk⟩ : ∃ k, N = k + 1 := ⟨N - 1, by omega⟩
      rw [hk, Nat.add_sub_cancel, pow_succ']
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx0 hx k) hx0
    calc ‖Rf N m₀ x‖ ≤ ‖x‖ ^ N * (‖x‖ + |m₀|) := h1
      _ ≤ (‖x‖ * U ^ (N - 1)) * (U + |m₀|) :=
          mul_le_mul hpow (by linarith) (by positivity) (by positivity)
      _ = ‖x‖ * (U ^ (N - 1) * (U + |m₀|)) := by ring
  have h1 := hf (I * node (anchor γ σ₀) ρ) (by rw [norm_mul, Complex.norm_I, one_mul]; exact hu)
  have h2 := hf (-I * node' (anchor γ σ₀) ρ)
    (by rw [norm_mul, norm_neg, Complex.norm_I, one_mul]; exact hu')
  rw [norm_mul, Complex.norm_I, one_mul] at h1
  rw [norm_mul, norm_neg, Complex.norm_I, one_mul] at h2
  calc (ZD.xiOrderNat ρ.val : ℝ)
        * (‖Rf N m₀ (I * node (anchor γ σ₀) ρ)‖ * ‖Rf N m₀ (-I * node' (anchor γ σ₀) ρ)‖)
      ≤ (ZD.xiOrderNat ρ.val : ℝ) * ((‖node (anchor γ σ₀) ρ‖ * (U ^ (N - 1) * (U + |m₀|)))
          * (‖node' (anchor γ σ₀) ρ‖ * (U ^ (N - 1) * (U + |m₀|)))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (norm_nonneg _) (by positivity))
          (Nat.cast_nonneg _)
    _ = C * ((ZD.xiOrderNat ρ.val : ℝ) * (‖node (anchor γ σ₀) ρ‖ * ‖node' (anchor γ σ₀) ρ‖)) := by
        rw [hC]; ring

/-! ## The node product, the FE distance product, and the leader -/

/-- The node product `P_ρ = ‖u_ρ‖ ‖u'_ρ‖` at the anchor over `γ`. -/
def nodeProd (γ σ₀ : ℝ) (ρ : Zero) : ℝ := ‖node (anchor γ σ₀) ρ‖ * ‖node' (anchor γ σ₀) ρ‖

theorem nodeProd_nonneg (γ σ₀ : ℝ) (ρ : Zero) : 0 ≤ nodeProd γ σ₀ ρ :=
  mul_nonneg (norm_nonneg _) (norm_nonneg _)

/-- The FE distance product `F_s(ρ) = ‖s − ρ‖ · ‖(1 − s̄) − ρ‖` in the chart, `s = σ₀ + iγ`. -/
def feDist (γ σ₀ : ℝ) (ρ : Zero) : ℝ :=
  ‖(σ₀ : ℂ) + (γ : ℂ) * I - ρ.val‖ * ‖((1 - σ₀ : ℝ) : ℂ) + (γ : ℂ) * I - ρ.val‖

theorem nodeProd_eq_inv_feDist (γ σ₀ : ℝ) (ρ : Zero) :
    nodeProd γ σ₀ ρ = (feDist γ σ₀ ρ)⁻¹ := by
  unfold nodeProd feDist
  rw [node_norm, node'_norm, chart_anchor, chart_anchor_conj, mul_inv]

/-- At its own ordinate, the pair's FE distance product is `D₀ = (σ₀ − β)(σ₀ − 1 + β)`. -/
theorem feDist_self (ρ : Zero) {σ₀ : ℝ} (h : 1 < σ₀) :
    feDist ρ.val.im σ₀ ρ = (σ₀ - ρ.val.re) * (σ₀ - 1 + ρ.val.re) := by
  unfold feDist
  have e1 : (σ₀ : ℂ) + (ρ.val.im : ℂ) * I - ρ.val = ((σ₀ - ρ.val.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp
  have e2 : ((1 - σ₀ : ℝ) : ℂ) + (ρ.val.im : ℂ) * I - ρ.val = ((1 - σ₀ - ρ.val.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp
  have hβ1 : ρ.val.re < 1 := ρ.2.2.1
  have hβ0 : 0 < ρ.val.re := ρ.2.1
  rw [e1, e2, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (by linarith), abs_of_neg (by linarith)]
  ring

/-- Zeros at height distance `≥ 1` from the anchor have FE distance product `≥ 1`. -/
theorem feDist_ge_one_of_far {γ σ₀ : ℝ} {ρ : Zero} (hfar : 1 ≤ |ρ.val.im - γ|) :
    1 ≤ feDist γ σ₀ ρ := by
  unfold feDist
  have h1 : |((σ₀ : ℂ) + (γ : ℂ) * I - ρ.val).im| ≤ ‖(σ₀ : ℂ) + (γ : ℂ) * I - ρ.val‖ :=
    Complex.abs_im_le_norm _
  have h2 : |(((1 - σ₀ : ℝ) : ℂ) + (γ : ℂ) * I - ρ.val).im|
      ≤ ‖((1 - σ₀ : ℝ) : ℂ) + (γ : ℂ) * I - ρ.val‖ := Complex.abs_im_le_norm _
  have e1 : ((σ₀ : ℂ) + (γ : ℂ) * I - ρ.val).im = γ - ρ.val.im := by simp
  have e2 : (((1 - σ₀ : ℝ) : ℂ) + (γ : ℂ) * I - ρ.val).im = γ - ρ.val.im := by simp
  rw [e1] at h1
  rw [e2] at h2
  rw [abs_sub_comm] at hfar
  have hn1 : 1 ≤ ‖(σ₀ : ℂ) + (γ : ℂ) * I - ρ.val‖ := hfar.trans h1
  have hn2 : 1 ≤ ‖((1 - σ₀ : ℝ) : ℂ) + (γ : ℂ) * I - ρ.val‖ := hfar.trans h2
  calc (1 : ℝ) = 1 * 1 := by ring
    _ ≤ _ := mul_le_mul hn1 hn2 zero_le_one (by linarith)

/-- **On-line zeros never lead at the anchor over an off-line zero**: their FE distance product is
at least `(σ₀−½)²`, while the off-line zero's own is `(σ₀−½)² − y² `. -/
theorem feDist_online_ge {γ σ₀ : ℝ} {ρ' : Zero} (hon : ρ'.val.re = 1 / 2) (h : 1 < σ₀) :
    (σ₀ - 1 / 2) ^ 2 ≤ feDist γ σ₀ ρ' := by
  unfold feDist
  have h1 : |((σ₀ : ℂ) + (γ : ℂ) * I - ρ'.val).re| ≤ ‖(σ₀ : ℂ) + (γ : ℂ) * I - ρ'.val‖ :=
    Complex.abs_re_le_norm _
  have h2 : |(((1 - σ₀ : ℝ) : ℂ) + (γ : ℂ) * I - ρ'.val).re|
      ≤ ‖((1 - σ₀ : ℝ) : ℂ) + (γ : ℂ) * I - ρ'.val‖ := Complex.abs_re_le_norm _
  have e1 : ((σ₀ : ℂ) + (γ : ℂ) * I - ρ'.val).re = σ₀ - 1 / 2 := by simp [hon]
  have e2 : (((1 - σ₀ : ℝ) : ℂ) + (γ : ℂ) * I - ρ'.val).re = 1 - σ₀ - 1 / 2 := by simp [hon]
  rw [e1, abs_of_pos (by linarith)] at h1
  rw [e2, abs_of_neg (by linarith)] at h2
  have h2' : σ₀ - 1 / 2 ≤ ‖((1 - σ₀ : ℝ) : ℂ) + (γ : ℂ) * I - ρ'.val‖ := by linarith
  calc (σ₀ - 1 / 2) ^ 2 = (σ₀ - 1 / 2) * (σ₀ - 1 / 2) := by ring
    _ ≤ _ := mul_le_mul h1 h2' (by linarith) (norm_nonneg _)

theorem D₀_lt_sq {σ₀ β : ℝ} (hoff : 1 / 2 < β) :
    (σ₀ - β) * (σ₀ - 1 + β) < (σ₀ - 1 / 2) ^ 2 := by
  nlinarith

/-- The leader hypothesis: at the anchor over its own ordinate, `ρ`'s pair has strictly the
smallest FE distance product among all zeros other than `ρ` and its FE partner. -/
def StrictLeader (ρ : Zero) (σ₀ : ℝ) : Prop :=
  ∀ ρ' : Zero, ρ' ≠ ρ → ρ' ≠ feReflectZ ρ →
    (σ₀ - ρ.val.re) * (σ₀ - 1 + ρ.val.re) < feDist ρ.val.im σ₀ ρ'

/-! ## Maximal depth implies the strict-leader hypothesis -/

/-- The depth of a zero: its distance from the critical line. -/
def Depth (ρ : Zero) : ℝ := |ρ.val.re - 1 / 2|

/-- `ρ` has maximal depth among all nontrivial zeros. -/
def MaxDepth (ρ : Zero) : Prop := ∀ ρ' : Zero, Depth ρ' ≤ Depth ρ

/-- The FE distance product at a zero's own ordinate is `A² − depth²`, `A = σ₀ − ½`. -/
theorem feDist_self_eq_sq_sub_depth (ρ : Zero) (σ₀ : ℝ) :
    (σ₀ - ρ.val.re) * (σ₀ - 1 + ρ.val.re) = (σ₀ - 1 / 2) ^ 2 - Depth ρ ^ 2 := by
  unfold Depth
  rw [sq_abs]
  ring

/-- Both chart factors are positive for `σ₀ > 1`. -/
theorem chart_factors_pos {σ₀ : ℝ} (h : 1 < σ₀) (ρ : Zero) :
    0 < σ₀ - ρ.val.re ∧ 0 < σ₀ - 1 + ρ.val.re := by
  have h1 : ρ.val.re < 1 := ρ.2.2.1
  have h0 : 0 < ρ.val.re := ρ.2.1
  constructor <;> linarith

/-- **Maximal depth ⇒ strict leader.**  At the anchor over a deepest zero's own ordinate, every
other zero (bar its FE partner) has a strictly larger FE distance product: off the ordinate the
imaginary offset makes both factors strictly larger, and on the ordinate a strictly smaller depth
makes the product larger. -/
theorem strictLeader_of_maxDepth {ρ : Zero} (hmax : MaxDepth ρ) {σ₀ : ℝ} (h1 : 1 < σ₀) :
    StrictLeader ρ σ₀ := by
  intro ρ' hne1 hne2
  obtain ⟨hp1, hp2⟩ := chart_factors_pos h1 ρ'
  obtain ⟨hq1, hq2⟩ := chart_factors_pos h1 ρ
  set z1 : ℂ := (σ₀ : ℂ) + (ρ.val.im : ℂ) * I - ρ'.val with hz1
  set z2 : ℂ := ((1 - σ₀ : ℝ) : ℂ) + (ρ.val.im : ℂ) * I - ρ'.val with hz2
  have hre1 : z1.re = σ₀ - ρ'.val.re := by rw [hz1]; simp
  have hre2 : z2.re = 1 - σ₀ - ρ'.val.re := by rw [hz2]; simp
  have him1 : z1.im = ρ.val.im - ρ'.val.im := by rw [hz1]; simp
  have him2 : z2.im = ρ.val.im - ρ'.val.im := by rw [hz2]; simp
  -- the depth comparison gives `D(ρ') ≥ D(ρ)`
  have hD : (σ₀ - ρ.val.re) * (σ₀ - 1 + ρ.val.re) ≤ (σ₀ - ρ'.val.re) * (σ₀ - 1 + ρ'.val.re) := by
    rw [feDist_self_eq_sq_sub_depth ρ σ₀, feDist_self_eq_sq_sub_depth ρ' σ₀]
    have hd := hmax ρ'
    have hd0 : 0 ≤ Depth ρ' := abs_nonneg _
    nlinarith
  by_cases hΔ : ρ.val.im - ρ'.val.im = 0
  · -- same ordinate: the product is exactly `D(ρ')`, and equality with `D(ρ)` is excluded
    have e1 : ‖z1‖ = σ₀ - ρ'.val.re := by
      have : z1 = ((σ₀ - ρ'.val.re : ℝ) : ℂ) := by
        apply Complex.ext
        · rw [hre1, Complex.ofReal_re]
        · rw [him1, Complex.ofReal_im]; exact hΔ
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp1]
    have e2 : ‖z2‖ = σ₀ - 1 + ρ'.val.re := by
      have : z2 = ((1 - σ₀ - ρ'.val.re : ℝ) : ℂ) := by
        apply Complex.ext
        · rw [hre2, Complex.ofReal_re]
        · rw [him2, Complex.ofReal_im]; exact hΔ
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
      ring
    unfold feDist
    rw [← hz1, ← hz2, e1, e2]
    rcases lt_or_eq_of_le hD with hlt | heq
    · exact hlt
    · -- equal products at equal ordinate: `ρ'` is `ρ` or its FE partner
      exfalso
      have hdepth : Depth ρ' = Depth ρ := by
        rw [feDist_self_eq_sq_sub_depth ρ σ₀, feDist_self_eq_sq_sub_depth ρ' σ₀] at heq
        have h0 : Depth ρ ^ 2 = Depth ρ' ^ 2 := by linarith
        have hd0 : (0 : ℝ) ≤ Depth ρ := abs_nonneg _
        have hd0' : (0 : ℝ) ≤ Depth ρ' := abs_nonneg _
        exact le_antisymm (hmax ρ') (by nlinarith)
      have him : ρ'.val.im = ρ.val.im := by linarith [hΔ]
      unfold Depth at hdepth
      rcases abs_eq_abs.mp hdepth with hc | hc
      · exact hne1 (Subtype.ext (Complex.ext (by linarith) him))
      · refine hne2 (Subtype.ext ?_)
        rw [feReflectZ_val]
        exact Complex.ext (by rw [feReflect_re]; linarith) (by rw [feReflect_im]; exact him)
  · -- off the ordinate: both factors are strictly larger
    have hs1 : σ₀ - ρ'.val.re < ‖z1‖ := by
      have := Complex.abs_re_lt_norm.mpr (by rw [him1]; exact hΔ)
      rw [hre1, abs_of_pos hp1] at this
      exact this
    have hs2 : σ₀ - 1 + ρ'.val.re < ‖z2‖ := by
      have := Complex.abs_re_lt_norm.mpr (by rw [him2]; exact hΔ)
      rw [hre2, abs_of_neg (by linarith)] at this
      linarith
    unfold feDist
    rw [← hz1, ← hz2]
    calc (σ₀ - ρ.val.re) * (σ₀ - 1 + ρ.val.re)
        ≤ (σ₀ - ρ'.val.re) * (σ₀ - 1 + ρ'.val.re) := hD
      _ < ‖z1‖ * ‖z2‖ := by nlinarith
/-! ## The main theorem: a strict off-line leader forces a negative form -/

theorem feReflectZ_ne_self {ρ : Zero} (hoff : 1 / 2 < ρ.val.re) : ρ ≠ feReflectZ ρ := by
  intro h
  have := congrArg (fun x : Zero => x.val.re) h
  simp only [feReflectZ_val, feReflect_re] at this
  linarith

theorem exists_primeAnchorForm_neg_of_leader {ρ : Zero} (hoff : 1 / 2 < ρ.val.re) {σ₀ : ℝ}
    (h1 : 1 < σ₀) (h2 : σ₀ < 3 / 2) (hlead : StrictLeader ρ σ₀) :
    ∃ N : ℕ, 1 ≤ N ∧ ∃ m₀ : ℝ, (primeAnchorForm (anchor ρ.val.im σ₀) N m₀).re < 0 := by
  classical
  have hβ1 : ρ.val.re < 1 := ρ.2.2.1
  have hσβ : 0 < σ₀ - ρ.val.re := by linarith
  have hσβ' : 0 < σ₀ - 1 + ρ.val.re := by linarith
  -- the pair nodes and the midpoint test root
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = (σ₀ - ρ.val.re)⁻¹ := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = (σ₀ - 1 + ρ.val.re)⁻¹ := ⟨_, rfl⟩
  have ha0 : 0 < a := by rw [ha]; positivity
  have hb0 : 0 < b := by rw [hb]; positivity
  have hba : b < a := by
    rw [ha, hb]
    apply inv_strictAnti₀ hσβ
    linarith
  obtain ⟨m₀, hm₀⟩ : ∃ m₀ : ℝ, m₀ = (a + b) / 2 := ⟨_, rfl⟩
  have hm₀a : m₀ < a := by rw [hm₀]; linarith
  have hbm₀ : b < m₀ := by rw [hm₀]; linarith
  -- D₀ and a·b
  obtain ⟨D₀, hD₀⟩ : ∃ D : ℝ, D = (σ₀ - ρ.val.re) * (σ₀ - 1 + ρ.val.re) := ⟨_, rfl⟩
  have hD₀pos : 0 < D₀ := by rw [hD₀]; positivity
  have hD₀lt1 : D₀ < 1 := by
    rw [hD₀]
    have := D₀_lt_sq (σ₀ := σ₀) hoff
    nlinarith
  have hab : a * b = D₀⁻¹ := by rw [ha, hb, hD₀, mul_inv]
  have h1ab : 1 < a * b := by
    rw [hab]
    exact one_lt_inv_iff₀.mpr ⟨hD₀pos, hD₀lt1⟩
  -- the near zeros form a finite set
  have hnear_fin : {ρ' : Zero | |ρ'.val.im - ρ.val.im| ≤ 1 ∧ ρ' ≠ ρ ∧ ρ' ≠ feReflectZ ρ}.Finite := by
    apply (CriticalLinePhasor.StBridge.finite_smallZeros (|ρ.val.im| + 2)).subset
    intro ρ' hρ'
    simp only [Set.mem_ofPred_eq] at hρ' ⊢
    have hn := Complex.norm_le_abs_re_add_abs_im ρ'.val
    have hre : |ρ'.val.re| < 1 := by rw [abs_of_pos ρ'.2.1]; exact ρ'.2.2.1
    have him : |ρ'.val.im| ≤ |ρ.val.im| + 1 := by
      have := abs_sub_abs_le_abs_sub ρ'.val.im ρ.val.im
      linarith [hρ'.1]
    linarith
  -- the uniform node-product bound `K < a b` over all other zeros
  obtain ⟨K, hK0, hKab, hKle⟩ : ∃ K : ℝ, 0 < K ∧ K < a * b ∧
      ∀ ρ' : Zero, ρ' ≠ ρ → ρ' ≠ feReflectZ ρ → nodeProd ρ.val.im σ₀ ρ' ≤ K := by
    have hlt : ∀ ρ' : Zero, ρ' ≠ ρ → ρ' ≠ feReflectZ ρ → nodeProd ρ.val.im σ₀ ρ' < a * b := by
      intro ρ' hne1 hne2
      rw [nodeProd_eq_inv_feDist, hab]
      apply inv_strictAnti₀ hD₀pos
      rw [hD₀]
      exact hlead ρ' hne1 hne2
    have hfar : ∀ ρ' : Zero, ¬ |ρ'.val.im - ρ.val.im| ≤ 1 → nodeProd ρ.val.im σ₀ ρ' ≤ 1 := by
      intro ρ' hρ'
      rw [nodeProd_eq_inv_feDist]
      rw [not_le] at hρ'
      exact inv_le_one_of_one_le₀ (feDist_ge_one_of_far hρ'.le)
    rcases hnear_fin.toFinset.eq_empty_or_nonempty with hemp | hne
    · refine ⟨1, one_pos, h1ab, fun ρ' hne1 hne2 => ?_⟩
      by_cases hin : |ρ'.val.im - ρ.val.im| ≤ 1
      · exfalso
        have hmem : ρ' ∈ hnear_fin.toFinset := hnear_fin.mem_toFinset.mpr ⟨hin, hne1, hne2⟩
        rw [hemp] at hmem
        exact Finset.notMem_empty _ hmem
      · exact hfar ρ' hin
    · obtain ⟨ρm, hρm, hmax⟩ := Finset.exists_max_image hnear_fin.toFinset
        (nodeProd ρ.val.im σ₀) hne
      have hρm' := hnear_fin.mem_toFinset.mp hρm
      refine ⟨max 1 (nodeProd ρ.val.im σ₀ ρm), lt_max_of_lt_left one_pos, ?_,
        fun ρ' hne1 hne2 => ?_⟩
      · exact max_lt h1ab (hlt ρm hρm'.2.1 hρm'.2.2)
      · by_cases hin : |ρ'.val.im - ρ.val.im| ≤ 1
        · have hmem : ρ' ∈ hnear_fin.toFinset := hnear_fin.mem_toFinset.mpr ⟨hin, hne1, hne2⟩
          exact le_max_of_le_right (hmax ρ' hmem)
        · exact le_max_of_le_left (hfar ρ' hin)
  -- constants
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = (ZD.xiOrderNat ρ.val : ℝ) := ⟨_, rfl⟩
  have hm0 : 0 < m := by rw [hm]; exact_mod_cast ZD.xiOrderNat_pos_of_mem_NontrivialZeros ρ.2
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = 2 * m * (a - m₀) * (m₀ - b) := ⟨_, rfl⟩
  have hc0 : 0 < c := by
    rw [hc]
    exact mul_pos (mul_pos (mul_pos two_pos hm0) (by linarith)) (by linarith)
  obtain ⟨U, hU⟩ : ∃ U : ℝ, U = (σ₀ - 1)⁻¹ := ⟨_, rfl⟩
  have hU0 : 0 ≤ U := by rw [hU]; positivity
  have hSsum : Summable (fun ρ' : Zero => (ZD.xiOrderNat ρ'.val : ℝ) * nodeProd ρ.val.im σ₀ ρ') :=
    summable_node_product (γ := ρ.val.im) h1
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = ∑' ρ' : Zero, (ZD.xiOrderNat ρ'.val : ℝ) * nodeProd ρ.val.im σ₀ ρ' :=
    ⟨_, rfl⟩
  have hS0 : 0 ≤ S := by
    rw [hS]
    exact tsum_nonneg (fun ρ' => mul_nonneg (Nat.cast_nonneg _) (nodeProd_nonneg _ _ _))
  obtain ⟨Ct, hCt⟩ : ∃ Ct : ℝ, Ct = (U + |m₀|) ^ 2 * S := ⟨_, rfl⟩
  have hCt0 : 0 ≤ Ct := by rw [hCt]; positivity
  -- choose the order `N`
  have hratio : 1 < a * b / K := by rw [lt_div_iff₀ hK0]; linarith
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp
    ((tendsto_pow_atTop_atTop_of_one_lt hratio).eventually_gt_atTop (Ct / (c * K)))
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = max N₀ 1 := ⟨_, rfl⟩
  have hN1 : 1 ≤ N := by rw [hN]; exact le_max_right _ _
  have hNbig : Ct / (c * K) < (a * b / K) ^ N := hN₀ N (by rw [hN]; exact le_max_left _ _)
  refine ⟨N, hN1, m₀, ?_⟩
  -- split off the pair
  have hsum := summable_primeAnchorTerm (γ := ρ.val.im) h1 hN1 m₀
  have hne : ρ ≠ feReflectZ ρ := feReflectZ_ne_self hoff
  have hsplit := hsum.sum_add_tsum_compl (s := {ρ, feReflectZ ρ})
  have hpairval : ∑ x ∈ ({ρ, feReflectZ ρ} : Finset Zero), primeAnchorTerm (anchor ρ.val.im σ₀) N m₀ x
      = ((-(c * (a * b) ^ N) : ℝ) : ℂ) := by
    rw [Finset.sum_pair hne, pair_terms ρ σ₀ N m₀, ← ha, ← hb, ← hm]
    congr 1
    rw [hc]
    ring
  -- the tail bound
  have htail : ‖∑' x : ↑((↑({ρ, feReflectZ ρ} : Finset Zero) : Set Zero)ᶜ),
      primeAnchorTerm (anchor ρ.val.im σ₀) N m₀ x.val‖ ≤ Ct * K ^ (N - 1) := by
    have hterm : ∀ x : ↑((↑({ρ, feReflectZ ρ} : Finset Zero) : Set Zero)ᶜ),
        ‖primeAnchorTerm (anchor ρ.val.im σ₀) N m₀ x.val‖
          ≤ ((U + |m₀|) ^ 2 * K ^ (N - 1))
              * ((ZD.xiOrderNat x.val.val : ℝ) * nodeProd ρ.val.im σ₀ x.val) := by
      intro x
      have hxmem : x.val ∉ ({ρ, feReflectZ ρ} : Finset Zero) := by
        have := x.2
        simpa using this
      have hx1 : x.val ≠ ρ := fun h => hxmem (by rw [h]; exact Finset.mem_insert_self _ _)
      have hx2 : x.val ≠ feReflectZ ρ := fun h => hxmem
        (by rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
      have hK := hKle x.val hx1 hx2
      unfold primeAnchorTerm
      rw [norm_mul, norm_mul, Complex.norm_natCast]
      have hu := node_le (γ := ρ.val.im) h1 x.val
      have hu' := node'_le (γ := ρ.val.im) h1 x.val
      rw [← hU] at hu hu'
      have e1 : ‖Rf N m₀ (I * node (anchor ρ.val.im σ₀) x.val)‖
          ≤ ‖node (anchor ρ.val.im σ₀) x.val‖ ^ N * (U + |m₀|) := by
        have := Rf_norm_le N m₀ (I * node (anchor ρ.val.im σ₀) x.val)
        rw [norm_mul, Complex.norm_I, one_mul] at this
        exact this.trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
      have e2 : ‖Rf N m₀ (-I * node' (anchor ρ.val.im σ₀) x.val)‖
          ≤ ‖node' (anchor ρ.val.im σ₀) x.val‖ ^ N * (U + |m₀|) := by
        have := Rf_norm_le N m₀ (-I * node' (anchor ρ.val.im σ₀) x.val)
        rw [norm_mul, norm_neg, Complex.norm_I, one_mul] at this
        exact this.trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
      have hnp : nodeProd ρ.val.im σ₀ x.val ^ N ≤ nodeProd ρ.val.im σ₀ x.val * K ^ (N - 1) := by
        obtain ⟨k, hk⟩ : ∃ k, N = k + 1 := ⟨N - 1, by omega⟩
        rw [hk, Nat.add_sub_cancel, pow_succ']
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (nodeProd_nonneg _ _ _) hK k)
          (nodeProd_nonneg _ _ _)
      have hnn : 0 ≤ ‖node (anchor ρ.val.im σ₀) x.val‖ ^ N * (U + |m₀|) := by positivity
      calc (ZD.xiOrderNat x.val.val : ℝ)
            * (‖Rf N m₀ (I * node (anchor ρ.val.im σ₀) x.val)‖
              * ‖Rf N m₀ (-I * node' (anchor ρ.val.im σ₀) x.val)‖)
          ≤ (ZD.xiOrderNat x.val.val : ℝ)
            * ((‖node (anchor ρ.val.im σ₀) x.val‖ ^ N * (U + |m₀|))
              * (‖node' (anchor ρ.val.im σ₀) x.val‖ ^ N * (U + |m₀|))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul e1 e2 (norm_nonneg _) hnn) (Nat.cast_nonneg _)
        _ = (ZD.xiOrderNat x.val.val : ℝ) * (nodeProd ρ.val.im σ₀ x.val ^ N * (U + |m₀|) ^ 2) := by
            unfold nodeProd
            ring
        _ ≤ (ZD.xiOrderNat x.val.val : ℝ)
            * ((nodeProd ρ.val.im σ₀ x.val * K ^ (N - 1)) * (U + |m₀|) ^ 2) := by
            gcongr
        _ = ((U + |m₀|) ^ 2 * K ^ (N - 1))
              * ((ZD.xiOrderNat x.val.val : ℝ) * nodeProd ρ.val.im σ₀ x.val) := by ring
    have hsumc : Summable (fun x : ↑((↑({ρ, feReflectZ ρ} : Finset Zero) : Set Zero)ᶜ) =>
        primeAnchorTerm (anchor ρ.val.im σ₀) N m₀ x.val) := hsum.subtype _
    have hsumn := summable_norm_iff.mpr hsumc
    have hsumg : Summable (fun x : ↑((↑({ρ, feReflectZ ρ} : Finset Zero) : Set Zero)ᶜ) =>
        ((U + |m₀|) ^ 2 * K ^ (N - 1))
          * ((ZD.xiOrderNat x.val.val : ℝ) * nodeProd ρ.val.im σ₀ x.val)) :=
      (hSsum.subtype _).mul_left _
    calc ‖∑' x : ↑((↑({ρ, feReflectZ ρ} : Finset Zero) : Set Zero)ᶜ),
          primeAnchorTerm (anchor ρ.val.im σ₀) N m₀ x.val‖
        ≤ ∑' x : ↑((↑({ρ, feReflectZ ρ} : Finset Zero) : Set Zero)ᶜ),
            ‖primeAnchorTerm (anchor ρ.val.im σ₀) N m₀ x.val‖ := norm_tsum_le_tsum_norm hsumn
      _ ≤ ∑' x : ↑((↑({ρ, feReflectZ ρ} : Finset Zero) : Set Zero)ᶜ),
            ((U + |m₀|) ^ 2 * K ^ (N - 1))
              * ((ZD.xiOrderNat x.val.val : ℝ) * nodeProd ρ.val.im σ₀ x.val) :=
          hsumn.tsum_le_tsum hterm hsumg
      _ = ((U + |m₀|) ^ 2 * K ^ (N - 1)) * ∑' x : ↑((↑({ρ, feReflectZ ρ} : Finset Zero) : Set Zero)ᶜ),
            ((ZD.xiOrderNat x.val.val : ℝ) * nodeProd ρ.val.im σ₀ x.val) := tsum_mul_left
      _ ≤ ((U + |m₀|) ^ 2 * K ^ (N - 1)) * S := by
          rw [hS]
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact Summable.tsum_subtype_le
            (fun ρ' : Zero => (ZD.xiOrderNat ρ'.val : ℝ) * nodeProd ρ.val.im σ₀ ρ')
            _ (fun ρ' => mul_nonneg (Nat.cast_nonneg _) (nodeProd_nonneg _ _ _)) hSsum
      _ = Ct * K ^ (N - 1) := by rw [hCt]; ring
  -- assemble
  have hform : primeAnchorForm (anchor ρ.val.im σ₀) N m₀
      = ((-(c * (a * b) ^ N) : ℝ) : ℂ)
        + ∑' x : ↑((↑({ρ, feReflectZ ρ} : Finset Zero) : Set Zero)ᶜ),
            primeAnchorTerm (anchor ρ.val.im σ₀) N m₀ x.val := by
    unfold primeAnchorForm
    rw [← hsplit, hpairval]
  rw [hform, Complex.add_re, Complex.ofReal_re]
  have hre_le : (∑' x : ↑((↑({ρ, feReflectZ ρ} : Finset Zero) : Set Zero)ᶜ),
      primeAnchorTerm (anchor ρ.val.im σ₀) N m₀ x.val).re ≤ Ct * K ^ (N - 1) :=
    (Complex.re_le_norm _).trans htail
  have hkey : Ct * K ^ (N - 1) < c * (a * b) ^ N := by
    have hKN : K ^ N = K * K ^ (N - 1) := by
      obtain ⟨k, hk⟩ : ∃ k, N = k + 1 := ⟨N - 1, by omega⟩
      rw [hk, Nat.add_sub_cancel, pow_succ']
    rw [div_pow, div_lt_div_iff₀ (by positivity) (by positivity)] at hNbig
    -- hNbig : Ct * K ^ N < (a*b)^N * (c * K)
    rw [hKN] at hNbig
    have hK' : 0 < K := hK0
    nlinarith [hNbig, hK']
  linarith

/-! ## The criterion under attainment of the depth supremum -/

theorem Depth_feReflectZ (ρ : Zero) : Depth (feReflectZ ρ) = Depth ρ := by
  unfold Depth
  rw [feReflectZ_val, feReflect_re]
  rw [show (1 : ℝ) - ρ.val.re - 1 / 2 = -(ρ.val.re - 1 / 2) by ring, abs_neg]

theorem MaxDepth_feReflectZ {ρ : Zero} (h : MaxDepth ρ) : MaxDepth (feReflectZ ρ) := by
  intro ρ'
  rw [Depth_feReflectZ]
  exact h ρ'

/-- **A deepest off-line zero forces a negative form at its own prime-computable anchor.** -/
theorem exists_primeAnchorForm_neg_of_maxDepth {ρ : Zero} (hoff : 1 / 2 < ρ.val.re)
    (hmax : MaxDepth ρ) {σ₀ : ℝ} (h1 : 1 < σ₀) (h2 : σ₀ < 3 / 2) :
    ∃ N : ℕ, 1 ≤ N ∧ ∃ m₀ : ℝ, (primeAnchorForm (anchor ρ.val.im σ₀) N m₀).re < 0 :=
  exists_primeAnchorForm_neg_of_leader hoff h1 h2 (strictLeader_of_maxDepth hmax h1)

/-- **The prime-anchor seat criterion, under attainment of the depth supremum.**  If some zero has
maximal depth, then nonnegativity of the order-`N` FE-paired form at every anchor with
`1 < σ₀ < 3/2` — an absolutely convergent, prime-computable quantity — implies RH. -/
theorem rh_of_primeAnchorForm_nonneg (hattain : ∃ ρ : Zero, MaxDepth ρ)
    (hpos : ∀ γ σ₀ : ℝ, 1 < σ₀ → σ₀ < 3 / 2 → ∀ N : ℕ, 1 ≤ N → ∀ m₀ : ℝ,
      0 ≤ (primeAnchorForm (anchor γ σ₀) N m₀).re) :
    ∀ ρ ∈ ZD.NontrivialZeros, ρ.re = 1 / 2 := by
  obtain ⟨rhoA, hmax⟩ := hattain
  intro ρ hρ
  by_contra hne
  -- the maximal depth is positive, and we may take the deepest zero to the right of the line
  have hdepth_pos : 0 < Depth rhoA := by
    have hd : 0 < Depth ⟨ρ, hρ⟩ := by
      unfold Depth
      exact abs_pos.mpr (fun h => hne (by linarith [sub_eq_zero.mp h]))
    exact lt_of_lt_of_le hd (hmax ⟨ρ, hρ⟩)
  obtain ⟨rhoB, hoff, hmax'⟩ : ∃ σ : Zero, 1 / 2 < σ.val.re ∧ MaxDepth σ := by
    rcases lt_or_gt_of_ne (fun h : rhoA.val.re = 1 / 2 => by
      simp only [Depth, h, sub_self, abs_zero] at hdepth_pos
      exact lt_irrefl _ hdepth_pos) with hlt | hgt
    · refine ⟨feReflectZ rhoA, ?_, MaxDepth_feReflectZ hmax⟩
      rw [feReflectZ_val, feReflect_re]
      linarith
    · exact ⟨rhoA, hgt, hmax⟩
  obtain ⟨N, hN, m₀, hneg⟩ := exists_primeAnchorForm_neg_of_maxDepth hoff hmax'
    (σ₀ := 5 / 4) (by norm_num) (by norm_num)
  exact absurd (hpos rhoB.val.im (5 / 4) (by norm_num) (by norm_num) N hN m₀) (not_le.mpr hneg)

end CriticalLinePhasor.SeatPrimeAnchor

#print axioms CriticalLinePhasor.SeatPrimeAnchor.primeAnchorForm_re_nonneg_of_online
#print axioms CriticalLinePhasor.SeatPrimeAnchor.strictLeader_of_maxDepth
#print axioms CriticalLinePhasor.SeatPrimeAnchor.exists_primeAnchorForm_neg_of_maxDepth
#print axioms CriticalLinePhasor.SeatPrimeAnchor.rh_of_primeAnchorForm_nonneg
