import Mathlib
import RequestProject.SeatPrimeAnchor

/-!
# The prime-anchor seat as a Hermitian form: the attainment gap closed (ledger 548)

`SeatPrimeAnchor.lean` proved RH ⟺ nonnegativity of the order-`N` FE-paired form along the
real test family `x^N (x − m₀)` at anchors `1 < σ₀ < 3/2`, with the ⟸ direction resting on the
attainment of the depth supremum (`rh_of_primeAnchorForm_nonneg`, hypothesis `∃ ρ, MaxDepth ρ`).
This file removes that hypothesis by widening the test family to every polynomial `R ∈ ℂ[y]` with
`R(0) = 0`.  With the twisted nodes `x_ρ = 1/(s − ρ)` and `x'_ρ = 1/(ρ − (1 − s̄))` the form is

  `Q_w(R) = Σ_ρ m_ρ · conj(R(conj x_ρ)) · R(x'_ρ)`,

which is the Hermitian form `Σ_ρ m_ρ (Σ_j v̄_j u_ρ^{j+1})(Σ_k v_k u'_ρ^{k+1})` of the ledger in the
coordinates `R(y) = Σ_j v_j (i y)^{j+1}`; for real `R` it is the compiled form
(`hermTerm_real_family`).

* On the line `x'_ρ = conj x_ρ`, so every term is `m_ρ |R(conj x_ρ)|² ≥ 0`
  (`hermForm_re_nonneg_of_online`) — for every complex polynomial `R`.
* Off the line no extremality is needed.  At the anchor over ANY off-line zero `ρ₀` take

    `R_N(y) = y^N · Π_{ρ' ∈ F} (y − x'_{ρ'}) · (y − μ)`,

  `F` = the zeros within height `1` of the anchor other than the pair `{ρ₀, 1 − ρ̄₀}`.  The
  product annihilates every `ρ' ∈ F` (and, since the FE partner's nodes are `ρ'`'s conjugated and
  swapped, every partner too); zeros outside the band have node product `≤ 1`; and the pair
  contributes `2 m (ab)^N Re[G₀ (a − μ̄)(b − μ)]`, `a = 1/(σ₀−β₀) > b = 1/(σ₀−1+β₀)`,
  `G₀ = conj(A(a)) A(b) ≠ 0`.  The complex root `μ = b − η`, `η = −((a−b)/2) Ḡ₀/|G₀|`, makes the
  bracket `≤ −|G₀|(a−b)²/4 < 0`, and `ab > 1` makes the pair dominate the tail
  (`exists_hermForm_neg`).

Main theorem `rh_iff_hermForm_nonneg`: RH ⟺ `Re Q_w(R) ≥ 0` for every anchor `1 < σ₀ < 3/2` and
every `R` with `R(0) = 0` — unconditional in both directions.  No `sorry`, no `axiom`.
-/

open Complex Filter Topology
open CriticalLinePhasor.HilbertPolya
open CriticalLinePhasor.FoliatedGlobalPolarization
open CriticalLinePhasor.FoliatedPolarization (feReflect)
open CriticalLinePhasor.SeatPrimeAnchor

noncomputable section

namespace CriticalLinePhasor.SeatPrimeAnchorHermitian

/-- The twisted node `x_ρ = i u_ρ = 1/(s − ρ)`. -/
def xnode (w : ℂ) (ρ : Zero) : ℂ := I * node w ρ

/-- The twisted conjugate node `x'_ρ = −i u'_ρ = 1/(ρ − (1 − s̄))`. -/
def xnode' (w : ℂ) (ρ : Zero) : ℂ := -I * node' w ρ

/-- The `ρ`-term of the Hermitian form along `R`. -/
def hermTerm (w : ℂ) (R : Polynomial ℂ) (ρ : Zero) : ℂ :=
  (ZD.xiOrderNat ρ.val : ℂ) *
    ((starRingEnd ℂ) (R.eval ((starRingEnd ℂ) (xnode w ρ))) * R.eval (xnode' w ρ))

/-- The Hermitian form along `R`. -/
def hermForm (w : ℂ) (R : Polynomial ℂ) : ℂ := ∑' ρ : Zero, hermTerm w R ρ

/-! ## Relation to the compiled real family -/

/-- Along the real test polynomial `X^N (X − m₀)` the Hermitian term is the compiled
`primeAnchorTerm`. -/
theorem hermTerm_real_family (w : ℂ) (N : ℕ) (m₀ : ℝ) (ρ : Zero) :
    hermTerm w (Polynomial.X ^ N * (Polynomial.X - Polynomial.C (m₀ : ℂ))) ρ
      = primeAnchorTerm w N m₀ ρ := by
  unfold hermTerm primeAnchorTerm Rf xnode xnode'
  simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_sub,
    Polynomial.eval_C, map_mul, map_pow, map_sub, Complex.conj_conj, Complex.conj_ofReal]

/-! ## Norms -/

theorem norm_xnode (w : ℂ) (ρ : Zero) : ‖xnode w ρ‖ = ‖node w ρ‖ := by
  unfold xnode
  rw [norm_mul, Complex.norm_I, one_mul]

theorem norm_xnode' (w : ℂ) (ρ : Zero) : ‖xnode' w ρ‖ = ‖node' w ρ‖ := by
  unfold xnode'
  rw [norm_mul, norm_neg, Complex.norm_I, one_mul]

theorem norm_hermTerm (w : ℂ) (R : Polynomial ℂ) (ρ : Zero) :
    ‖hermTerm w R ρ‖ = (ZD.xiOrderNat ρ.val : ℝ) *
      (‖R.eval ((starRingEnd ℂ) (xnode w ρ))‖ * ‖R.eval (xnode' w ρ)‖) := by
  unfold hermTerm
  rw [norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_conj]

/-! ## The on-line direction -/

theorem xnode'_eq_conj_of_online {w : ℂ} {ρ : Zero} (hρ : ρ.val.re = 1 / 2) :
    xnode' w ρ = (starRingEnd ℂ) (xnode w ρ) := by
  unfold xnode xnode'
  exact twisted_nodes_conj_of_online hρ

/-- On the line every term is `m_ρ |R(conj x_ρ)|² ≥ 0`, for every complex polynomial `R`. -/
theorem hermTerm_re_nonneg_of_online {w : ℂ} (R : Polynomial ℂ) {ρ : Zero}
    (hρ : ρ.val.re = 1 / 2) :
    0 ≤ (hermTerm w R ρ).re ∧ (hermTerm w R ρ).im = 0 := by
  unfold hermTerm
  rw [xnode'_eq_conj_of_online hρ, mul_comm ((starRingEnd ℂ) _), Complex.mul_conj,
    ← Complex.ofReal_natCast, ← Complex.ofReal_mul]
  constructor
  · rw [Complex.ofReal_re]
    exact mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _)
  · rw [Complex.ofReal_im]

/-- **The on-line direction**: if every zero is on the line, the Hermitian form is nonnegative at
every anchor along every polynomial. -/
theorem hermForm_re_nonneg_of_online {w : ℂ} (R : Polynomial ℂ)
    (hon : ∀ ρ ∈ ZD.NontrivialZeros, ρ.re = 1 / 2) :
    0 ≤ (hermForm w R).re := by
  unfold hermForm
  by_cases hsum : Summable (hermTerm w R)
  · rw [Complex.re_tsum hsum]
    exact tsum_nonneg (fun ρ => (hermTerm_re_nonneg_of_online R (hon ρ.val ρ.2)).1)
  · rw [tsum_eq_zero_of_not_summable hsum, Complex.zero_re]

/-! ## Chart formulas for the twisted nodes -/

theorem xnode_eq (w : ℂ) (ρ : Zero) : xnode w ρ = ((1 / 2 : ℂ) + I * w - ρ.val)⁻¹ := by
  unfold xnode node
  have h : (1 / 2 : ℂ) + I * w - ρ.val = -I * (spectralCoord ρ.val - w) := by
    unfold spectralCoord
    linear_combination (-(ρ.val - 1 / 2)) * I_sq
  rw [h, mul_inv, neg_I_inv]

theorem xnode'_eq (w : ℂ) (ρ : Zero) :
    xnode' w ρ = (ρ.val - ((1 / 2 : ℂ) + I * (starRingEnd ℂ) w))⁻¹ := by
  unfold xnode' node'
  have h : ρ.val - ((1 / 2 : ℂ) + I * (starRingEnd ℂ) w)
      = I * (spectralCoord ρ.val - (starRingEnd ℂ) w) := by
    unfold spectralCoord
    linear_combination (ρ.val - 1 / 2) * I_sq
  rw [h, mul_inv, Complex.inv_I]

theorem xnode_anchor (γ σ₀ : ℝ) (ρ : Zero) :
    xnode (anchor γ σ₀) ρ = ((σ₀ : ℂ) + (γ : ℂ) * I - ρ.val)⁻¹ := by
  rw [xnode_eq, chart_anchor]

theorem xnode'_anchor (γ σ₀ : ℝ) (ρ : Zero) :
    xnode' (anchor γ σ₀) ρ = (ρ.val - (((1 - σ₀ : ℝ) : ℂ) + (γ : ℂ) * I))⁻¹ := by
  rw [xnode'_eq, chart_anchor_conj]

/-- `x'` separates zeros. -/
theorem xnode'_injective (γ σ₀ : ℝ) {ρ ρ' : Zero}
    (h : xnode' (anchor γ σ₀) ρ' = xnode' (anchor γ σ₀) ρ) : ρ' = ρ := by
  rw [xnode'_anchor, xnode'_anchor, inv_inj, sub_left_inj] at h
  exact Subtype.ext h

/-- `x'_{ρ'} = x_ρ` at the anchor over `ρ`'s own ordinate forces `ρ'` to be the FE partner. -/
theorem eq_feReflectZ_of_xnode'_eq_xnode (σ₀ : ℝ) {ρ ρ' : Zero}
    (h : xnode' (anchor ρ.val.im σ₀) ρ' = xnode (anchor ρ.val.im σ₀) ρ) :
    ρ' = feReflectZ ρ := by
  rw [xnode'_anchor, xnode_anchor, inv_inj] at h
  apply Subtype.ext
  rw [feReflectZ_val]
  unfold feReflect
  apply Complex.ext
  · have := congrArg Complex.re h
    simp at this ⊢
    linarith
  · have := congrArg Complex.im h
    simp at this ⊢
    linarith

/-! ## The near band is finite -/

theorem near_finite (ρ : Zero) :
    {ρ' : Zero | |ρ'.val.im - ρ.val.im| ≤ 1 ∧ ρ' ≠ ρ ∧ ρ' ≠ feReflectZ ρ}.Finite := by
  apply (CriticalLinePhasor.StBridge.finite_smallZeros (|ρ.val.im| + 2)).subset
  intro ρ' hρ'
  simp only [Set.mem_ofPred_eq] at hρ' ⊢
  have hn := Complex.norm_le_abs_re_add_abs_im ρ'.val
  have hre : |ρ'.val.re| < 1 := by rw [abs_of_pos ρ'.2.1]; exact ρ'.2.2.1
  have him : |ρ'.val.im| ≤ |ρ.val.im| + 1 := by
    have := abs_sub_abs_le_abs_sub ρ'.val.im ρ.val.im
    linarith [hρ'.1]
  linarith

/-! ## Summability along polynomials without constant term -/

theorem summable_hermTerm_X_mul {γ σ₀ : ℝ} (h : 1 < σ₀) (T : Polynomial ℂ) :
    Summable (hermTerm (anchor γ σ₀) (Polynomial.X * T)) := by
  set U : ℝ := (σ₀ - 1)⁻¹ with hU
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℂ) U).exists_bound_of_continuousOn
    T.continuous.continuousOn
  have hB' : ∀ y : ℂ, ‖y‖ ≤ U → ‖T.eval y‖ ≤ max B 0 := fun y hy =>
    le_max_of_le_left (hB y (by rw [Metric.mem_closedBall, dist_zero_right]; exact hy))
  have hmaj := (summable_node_product (γ := γ) h).mul_left (max B 0 * max B 0)
  refine Summable.of_norm_bounded hmaj (fun ρ => ?_)
  rw [norm_hermTerm]
  have hu := node_le (γ := γ) h ρ
  have hu' := node'_le (γ := γ) h ρ
  rw [← hU] at hu hu'
  have e1 : ‖(Polynomial.X * T).eval ((starRingEnd ℂ) (xnode (anchor γ σ₀) ρ))‖
      ≤ ‖node (anchor γ σ₀) ρ‖ * max B 0 := by
    rw [Polynomial.eval_mul, Polynomial.eval_X, norm_mul, Complex.norm_conj, norm_xnode]
    exact mul_le_mul_of_nonneg_left
      (hB' _ (by rw [Complex.norm_conj, norm_xnode]; exact hu)) (norm_nonneg _)
  have e2 : ‖(Polynomial.X * T).eval (xnode' (anchor γ σ₀) ρ)‖
      ≤ ‖node' (anchor γ σ₀) ρ‖ * max B 0 := by
    rw [Polynomial.eval_mul, Polynomial.eval_X, norm_mul, norm_xnode']
    exact mul_le_mul_of_nonneg_left (hB' _ (by rw [norm_xnode']; exact hu')) (norm_nonneg _)
  calc (ZD.xiOrderNat ρ.val : ℝ)
        * (‖(Polynomial.X * T).eval ((starRingEnd ℂ) (xnode (anchor γ σ₀) ρ))‖
          * ‖(Polynomial.X * T).eval (xnode' (anchor γ σ₀) ρ)‖)
      ≤ (ZD.xiOrderNat ρ.val : ℝ)
        * ((‖node (anchor γ σ₀) ρ‖ * max B 0) * (‖node' (anchor γ σ₀) ρ‖ * max B 0)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul e1 e2 (norm_nonneg _) (by positivity))
          (Nat.cast_nonneg _)
    _ = max B 0 * max B 0
        * ((ZD.xiOrderNat ρ.val : ℝ) * (‖node (anchor γ σ₀) ρ‖ * ‖node' (anchor γ σ₀) ρ‖)) := by
        ring

/-- Every polynomial without constant term gives a summable form at anchors `σ₀ > 1`. -/
theorem summable_hermTerm_of_coeff_zero {γ σ₀ : ℝ} (h : 1 < σ₀) {R : Polynomial ℂ}
    (hR : R.coeff 0 = 0) : Summable (hermTerm (anchor γ σ₀) R) := by
  obtain ⟨T, hT⟩ := Polynomial.X_dvd_iff.mpr hR
  rw [hT]
  exact summable_hermTerm_X_mul h T

/-! ## The main theorem: an off-line zero forces a negative form at its own anchor -/

theorem exists_hermForm_neg {ρ : Zero} (hoff : 1 / 2 < ρ.val.re) {σ₀ : ℝ}
    (h1 : 1 < σ₀) (h2 : σ₀ < 3 / 2) :
    ∃ R : Polynomial ℂ, R.coeff 0 = 0 ∧ (hermForm (anchor ρ.val.im σ₀) R).re < 0 := by
  classical
  have hβ1 : ρ.val.re < 1 := ρ.2.2.1
  have hσβ : 0 < σ₀ - ρ.val.re := by linarith
  have hσβ' : 0 < σ₀ - 1 + ρ.val.re := by linarith
  -- the pair nodes `a > b > 0`, `ab > 1`
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = (σ₀ - ρ.val.re)⁻¹ := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = (σ₀ - 1 + ρ.val.re)⁻¹ := ⟨_, rfl⟩
  have ha0 : 0 < a := by rw [ha]; positivity
  have hb0 : 0 < b := by rw [hb]; positivity
  have hba : b < a := by
    rw [ha, hb]
    apply inv_strictAnti₀ hσβ
    linarith
  have h1ab : 1 < a * b := by
    have hD : (σ₀ - ρ.val.re) * (σ₀ - 1 + ρ.val.re) < 1 := by
      have := D₀_lt_sq (σ₀ := σ₀) hoff
      nlinarith
    have hDpos : 0 < (σ₀ - ρ.val.re) * (σ₀ - 1 + ρ.val.re) := by positivity
    rw [ha, hb, ← mul_inv]
    exact one_lt_inv_iff₀.mpr ⟨hDpos, hD⟩
  have hxa : xnode (anchor ρ.val.im σ₀) ρ = (a : ℂ) := by
    rw [ha]; exact twisted_node_self ρ σ₀
  have hxb : xnode' (anchor ρ.val.im σ₀) ρ = (b : ℂ) := by
    rw [hb]; exact twisted_node'_self ρ σ₀
  have hxa' : xnode (anchor ρ.val.im σ₀) (feReflectZ ρ) = (b : ℂ) := by
    rw [hb]; exact twisted_node_partner ρ σ₀
  have hxb' : xnode' (anchor ρ.val.im σ₀) (feReflectZ ρ) = (a : ℂ) := by
    rw [ha]; exact twisted_node'_partner ρ σ₀
  have hne : ρ ≠ feReflectZ ρ := feReflectZ_ne_self hoff
  -- the near band, minus the pair
  have hnear := near_finite ρ
  obtain ⟨F, hF⟩ : ∃ F : Finset Zero, F = hnear.toFinset := ⟨_, rfl⟩
  have hmemF : ∀ ρ', ρ' ∈ F ↔
      |ρ'.val.im - ρ.val.im| ≤ 1 ∧ ρ' ≠ ρ ∧ ρ' ≠ feReflectZ ρ := by
    intro ρ'
    rw [hF, Set.Finite.mem_toFinset]
    rfl
  -- the annihilator
  obtain ⟨A, hA⟩ : ∃ A : Polynomial ℂ,
      A = ∏ ρ' ∈ F, (Polynomial.X - Polynomial.C (xnode' (anchor ρ.val.im σ₀) ρ')) := ⟨_, rfl⟩
  have hAeval : ∀ y : ℂ, A.eval y = ∏ ρ' ∈ F, (y - xnode' (anchor ρ.val.im σ₀) ρ') := by
    intro y
    rw [hA, Polynomial.eval_prod]
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  have hAkill : ∀ ρ' ∈ F, A.eval (xnode' (anchor ρ.val.im σ₀) ρ') = 0 := by
    intro ρ' hρ'
    rw [hAeval]
    exact Finset.prod_eq_zero hρ' (sub_self _)
  have hAa : A.eval (a : ℂ) ≠ 0 := by
    rw [hAeval]
    apply Finset.prod_ne_zero_iff.mpr
    intro ρ' hρ'
    rw [sub_ne_zero, ← hxa]
    intro heq
    exact ((hmemF ρ').mp hρ').2.2 (eq_feReflectZ_of_xnode'_eq_xnode σ₀ heq.symm)
  have hAb : A.eval (b : ℂ) ≠ 0 := by
    rw [hAeval]
    apply Finset.prod_ne_zero_iff.mpr
    intro ρ' hρ'
    rw [sub_ne_zero, ← hxb]
    intro heq
    exact ((hmemF ρ').mp hρ').2.1 (xnode'_injective _ _ heq.symm)
  -- `G₀`, `η`, `μ`
  obtain ⟨G, hG⟩ : ∃ G : ℂ, G = (starRingEnd ℂ) (A.eval (a : ℂ)) * A.eval (b : ℂ) := ⟨_, rfl⟩
  have hG0 : G ≠ 0 := by
    rw [hG]
    exact mul_ne_zero ((map_ne_zero (starRingEnd ℂ)).mpr hAa) hAb
  have hGn : 0 < ‖G‖ := norm_pos_iff.mpr hG0
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = (a - b) / 2 := ⟨_, rfl⟩
  have hr0 : 0 < r := by rw [hr]; linarith
  obtain ⟨η, hη⟩ : ∃ η : ℂ, η = ((-r / ‖G‖ : ℝ) : ℂ) * (starRingEnd ℂ) G := ⟨_, rfl⟩
  have hGη : G * η = ((-(r * ‖G‖) : ℝ) : ℂ) := by
    rw [hη, mul_left_comm, Complex.mul_conj', ← Complex.ofReal_pow, ← Complex.ofReal_mul]
    congr 1
    field_simp
  have hηη : η * (starRingEnd ℂ) η = ((r ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj', ← Complex.ofReal_pow]
    congr 1
    rw [hη, norm_mul, Complex.norm_real, Complex.norm_conj, Real.norm_eq_abs, abs_div, abs_neg,
      abs_of_pos hr0, abs_of_pos hGn, div_mul_cancel₀ _ hGn.ne']
  obtain ⟨μ, hμ⟩ : ∃ μ : ℂ, μ = (b : ℂ) - η := ⟨_, rfl⟩
  -- the bracket bound: `Re[G (a − μ̄)(b − μ)] ≤ −c₀`
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : ℝ, c₀ = ‖G‖ * (a - b) ^ 2 / 4 := ⟨_, rfl⟩
  have hc₀0 : 0 < c₀ := by
    rw [hc₀]
    have : 0 < a - b := by linarith
    positivity
  have hbracket : (G * (((a : ℂ) - (starRingEnd ℂ) μ) * ((b : ℂ) - μ))).re ≤ -c₀ := by
    have e1 : (b : ℂ) - μ = η := by rw [hμ]; ring
    have e2 : (a : ℂ) - (starRingEnd ℂ) μ = ((a - b : ℝ) : ℂ) + (starRingEnd ℂ) η := by
      rw [hμ, map_sub, Complex.conj_ofReal]
      push_cast
      ring
    rw [e1, e2, show G * ((((a - b : ℝ) : ℂ) + (starRingEnd ℂ) η) * η)
        = ((a - b : ℝ) : ℂ) * (G * η) + (η * (starRingEnd ℂ) η) * G by ring, hGη, hηη,
      Complex.add_re, ← Complex.ofReal_mul, Complex.ofReal_re, Complex.re_ofReal_mul]
    have hre : G.re ≤ ‖G‖ := Complex.re_le_norm G
    rw [hc₀, hr]
    nlinarith [hre, hGn, sq_nonneg (a - b)]
  -- the test polynomial `S = A (X − μ)` and its bound on the node disc
  obtain ⟨S, hS⟩ : ∃ S : Polynomial ℂ, S = A * (Polynomial.X - Polynomial.C μ) := ⟨_, rfl⟩
  have hSeval : ∀ y : ℂ, S.eval y = A.eval y * (y - μ) := by
    intro y
    rw [hS]
    simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  set U : ℝ := (σ₀ - 1)⁻¹ with hU
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℂ) U).exists_bound_of_continuousOn
    S.continuous.continuousOn
  obtain ⟨Bp, hBp⟩ : ∃ Bp : ℝ, Bp = max B 0 := ⟨_, rfl⟩
  have hBp0 : 0 ≤ Bp := by rw [hBp]; exact le_max_right _ _
  have hSb : ∀ y : ℂ, ‖y‖ ≤ U → ‖S.eval y‖ ≤ Bp := fun y hy => by
    rw [hBp]
    exact le_max_of_le_left (hB y (by rw [Metric.mem_closedBall, dist_zero_right]; exact hy))
  -- constants
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = (ZD.xiOrderNat ρ.val : ℝ) := ⟨_, rfl⟩
  have hm0 : 0 < m := by rw [hm]; exact_mod_cast ZD.xiOrderNat_pos_of_mem_NontrivialZeros ρ.2
  have hSsum : Summable (fun ρ' : Zero => (ZD.xiOrderNat ρ'.val : ℝ) * nodeProd ρ.val.im σ₀ ρ') :=
    summable_node_product (γ := ρ.val.im) h1
  obtain ⟨Stot, hStot⟩ : ∃ s : ℝ,
      s = ∑' ρ' : Zero, (ZD.xiOrderNat ρ'.val : ℝ) * nodeProd ρ.val.im σ₀ ρ' := ⟨_, rfl⟩
  have hStot0 : 0 ≤ Stot := by
    rw [hStot]
    exact tsum_nonneg (fun ρ' => mul_nonneg (Nat.cast_nonneg _) (nodeProd_nonneg _ _ _))
  obtain ⟨Ct, hCt⟩ : ∃ Ct : ℝ, Ct = Bp ^ 2 * Stot := ⟨_, rfl⟩
  have hCt0 : 0 ≤ Ct := by rw [hCt]; positivity
  -- the order `N`
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp
    ((tendsto_pow_atTop_atTop_of_one_lt h1ab).eventually_gt_atTop (Ct / (2 * m * c₀)))
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = max N₀ 1 := ⟨_, rfl⟩
  have hN1 : 1 ≤ N := by rw [hN]; exact le_max_right _ _
  have hNbig : Ct / (2 * m * c₀) < (a * b) ^ N := hN₀ N (by rw [hN]; exact le_max_left _ _)
  have hkey : Ct < 2 * m * c₀ * (a * b) ^ N := by
    have := (div_lt_iff₀ (by positivity)).mp hNbig
    linarith
  -- the polynomial `R = X^N S`
  obtain ⟨R, hR⟩ : ∃ R : Polynomial ℂ, R = Polynomial.X ^ N * S := ⟨_, rfl⟩
  have hR0 : R.coeff 0 = 0 := by
    rw [hR, Polynomial.coeff_X_pow_mul', if_neg (by omega)]
  have hReval : ∀ y : ℂ, R.eval y = y ^ N * (A.eval y * (y - μ)) := by
    intro y
    rw [hR, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, hSeval]
  refine ⟨R, hR0, ?_⟩
  have hsum : Summable (hermTerm (anchor ρ.val.im σ₀) R) :=
    summable_hermTerm_of_coeff_zero h1 hR0
  -- the finite set `T = {ρ, partner} ∪ F`
  obtain ⟨T, hT⟩ : ∃ T : Finset Zero, T = insert ρ (insert (feReflectZ ρ) F) := ⟨_, rfl⟩
  have hρF : ρ ∉ F := fun h => ((hmemF ρ).mp h).2.1 rfl
  have hρ'F : feReflectZ ρ ∉ F := fun h => ((hmemF _).mp h).2.2 rfl
  have hρins : ρ ∉ insert (feReflectZ ρ) F := by
    rw [Finset.mem_insert, not_or]
    exact ⟨hne, hρF⟩
  -- zeros outside `T` are outside the band
  have hfar_of : ∀ y : Zero, y ∉ T → 1 < |y.val.im - ρ.val.im| := by
    intro y hy
    rw [hT, Finset.mem_insert, Finset.mem_insert, not_or, not_or] at hy
    by_contra hle
    exact hy.2.2 ((hmemF y).mpr ⟨not_lt.mp hle, hy.1, hy.2.1⟩)
  -- the pair
  have hz : hermTerm (anchor ρ.val.im σ₀) R ρ
      = ((m * (a * b) ^ N : ℝ) : ℂ)
        * (G * (((a : ℂ) - (starRingEnd ℂ) μ) * ((b : ℂ) - μ))) := by
    unfold hermTerm
    rw [hxa, hxb, Complex.conj_ofReal, hReval, hReval, hG, ← Complex.ofReal_natCast, ← hm]
    simp only [map_mul, map_pow, map_sub, Complex.conj_ofReal]
    push_cast
    ring
  have hz' : hermTerm (anchor ρ.val.im σ₀) R (feReflectZ ρ)
      = (starRingEnd ℂ) (hermTerm (anchor ρ.val.im σ₀) R ρ) := by
    unfold hermTerm
    rw [hxa, hxb, hxa', hxb', feReflectZ_val, xiOrderNat_feReflect]
    simp only [map_mul, Complex.conj_conj, Complex.conj_natCast, Complex.conj_ofReal]
    ring
  have hpair : hermTerm (anchor ρ.val.im σ₀) R ρ + hermTerm (anchor ρ.val.im σ₀) R (feReflectZ ρ)
      = ((2 * (hermTerm (anchor ρ.val.im σ₀) R ρ).re : ℝ) : ℂ) := by
    rw [hz', Complex.add_conj]
  have hzre : (hermTerm (anchor ρ.val.im σ₀) R ρ).re ≤ -(m * c₀ * (a * b) ^ N) := by
    rw [hz, Complex.re_ofReal_mul]
    have hpos : 0 ≤ m * (a * b) ^ N := by positivity
    calc m * (a * b) ^ N * (G * (((a : ℂ) - (starRingEnd ℂ) μ) * ((b : ℂ) - μ))).re
        ≤ m * (a * b) ^ N * (-c₀) := mul_le_mul_of_nonneg_left hbracket hpos
      _ = -(m * c₀ * (a * b) ^ N) := by ring
  -- the finite sum: the pair, and the annihilated band
  have hF0 : ∑ x ∈ F, hermTerm (anchor ρ.val.im σ₀) R x = 0 := by
    apply Finset.sum_eq_zero
    intro ρ' hρ'
    unfold hermTerm
    rw [hReval (xnode' (anchor ρ.val.im σ₀) ρ'), hAkill ρ' hρ']
    simp
  have hfin : ∑ x ∈ T, hermTerm (anchor ρ.val.im σ₀) R x
      = hermTerm (anchor ρ.val.im σ₀) R ρ + hermTerm (anchor ρ.val.im σ₀) R (feReflectZ ρ) := by
    rw [hT, Finset.sum_insert hρins, Finset.sum_insert hρ'F, hF0, add_zero]
  -- the tail: zeros outside the band have node product `≤ 1`
  have htail : ‖∑' x : ↑((↑T : Set Zero)ᶜ), hermTerm (anchor ρ.val.im σ₀) R x.val‖ ≤ Ct := by
    have hterm : ∀ x : ↑((↑T : Set Zero)ᶜ), ‖hermTerm (anchor ρ.val.im σ₀) R x.val‖
        ≤ Bp ^ 2 * ((ZD.xiOrderNat x.val.val : ℝ) * nodeProd ρ.val.im σ₀ x.val) := by
      intro x
      have hxT : x.val ∉ T := fun h => x.2 (Finset.mem_coe.mpr h)
      have hfar : 1 < |x.val.val.im - ρ.val.im| := hfar_of x.val hxT
      have hP1 : nodeProd ρ.val.im σ₀ x.val ≤ 1 := by
        rw [nodeProd_eq_inv_feDist]
        exact inv_le_one_of_one_le₀ (feDist_ge_one_of_far hfar.le)
      have hP0 : 0 ≤ nodeProd ρ.val.im σ₀ x.val := nodeProd_nonneg _ _ _
      have hu := node_le (γ := ρ.val.im) h1 x.val
      have hu' := node'_le (γ := ρ.val.im) h1 x.val
      rw [← hU] at hu hu'
      rw [norm_hermTerm]
      have e1 : ‖R.eval ((starRingEnd ℂ) (xnode (anchor ρ.val.im σ₀) x.val))‖
          ≤ ‖node (anchor ρ.val.im σ₀) x.val‖ ^ N * Bp := by
        rw [hReval, ← hSeval, norm_mul, norm_pow, Complex.norm_conj, norm_xnode]
        exact mul_le_mul_of_nonneg_left
          (hSb _ (by rw [Complex.norm_conj, norm_xnode]; exact hu)) (by positivity)
      have e2 : ‖R.eval (xnode' (anchor ρ.val.im σ₀) x.val)‖
          ≤ ‖node' (anchor ρ.val.im σ₀) x.val‖ ^ N * Bp := by
        rw [hReval, ← hSeval, norm_mul, norm_pow, norm_xnode']
        exact mul_le_mul_of_nonneg_left (hSb _ (by rw [norm_xnode']; exact hu')) (by positivity)
      have hnp : nodeProd ρ.val.im σ₀ x.val ^ N ≤ nodeProd ρ.val.im σ₀ x.val :=
        pow_le_of_le_one hP0 hP1 (by omega)
      calc (ZD.xiOrderNat x.val.val : ℝ)
            * (‖R.eval ((starRingEnd ℂ) (xnode (anchor ρ.val.im σ₀) x.val))‖
              * ‖R.eval (xnode' (anchor ρ.val.im σ₀) x.val)‖)
          ≤ (ZD.xiOrderNat x.val.val : ℝ)
            * ((‖node (anchor ρ.val.im σ₀) x.val‖ ^ N * Bp)
              * (‖node' (anchor ρ.val.im σ₀) x.val‖ ^ N * Bp)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul e1 e2 (norm_nonneg _) (by positivity))
              (Nat.cast_nonneg _)
        _ = (ZD.xiOrderNat x.val.val : ℝ) * (nodeProd ρ.val.im σ₀ x.val ^ N * Bp ^ 2) := by
            unfold nodeProd
            ring
        _ ≤ (ZD.xiOrderNat x.val.val : ℝ) * (nodeProd ρ.val.im σ₀ x.val * Bp ^ 2) := by
            gcongr
        _ = Bp ^ 2 * ((ZD.xiOrderNat x.val.val : ℝ) * nodeProd ρ.val.im σ₀ x.val) := by ring
    have hsumc : Summable (fun x : ↑((↑T : Set Zero)ᶜ) =>
        hermTerm (anchor ρ.val.im σ₀) R x.val) := hsum.subtype _
    have hsumn := summable_norm_iff.mpr hsumc
    have hsumg : Summable (fun x : ↑((↑T : Set Zero)ᶜ) =>
        Bp ^ 2 * ((ZD.xiOrderNat x.val.val : ℝ) * nodeProd ρ.val.im σ₀ x.val)) :=
      (hSsum.subtype _).mul_left _
    calc ‖∑' x : ↑((↑T : Set Zero)ᶜ), hermTerm (anchor ρ.val.im σ₀) R x.val‖
        ≤ ∑' x : ↑((↑T : Set Zero)ᶜ), ‖hermTerm (anchor ρ.val.im σ₀) R x.val‖ :=
          norm_tsum_le_tsum_norm hsumn
      _ ≤ ∑' x : ↑((↑T : Set Zero)ᶜ),
            Bp ^ 2 * ((ZD.xiOrderNat x.val.val : ℝ) * nodeProd ρ.val.im σ₀ x.val) :=
          hsumn.tsum_le_tsum hterm hsumg
      _ = Bp ^ 2 * ∑' x : ↑((↑T : Set Zero)ᶜ),
            ((ZD.xiOrderNat x.val.val : ℝ) * nodeProd ρ.val.im σ₀ x.val) := tsum_mul_left
      _ ≤ Bp ^ 2 * Stot := by
          rw [hStot]
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact Summable.tsum_subtype_le
            (fun ρ' : Zero => (ZD.xiOrderNat ρ'.val : ℝ) * nodeProd ρ.val.im σ₀ ρ')
            _ (fun ρ' => mul_nonneg (Nat.cast_nonneg _) (nodeProd_nonneg _ _ _)) hSsum
      _ = Ct := by rw [hCt]
  -- assemble
  have hsplit := hsum.sum_add_tsum_compl (s := T)
  have hform : hermForm (anchor ρ.val.im σ₀) R
      = ((2 * (hermTerm (anchor ρ.val.im σ₀) R ρ).re : ℝ) : ℂ)
        + ∑' x : ↑((↑T : Set Zero)ᶜ), hermTerm (anchor ρ.val.im σ₀) R x.val := by
    unfold hermForm
    rw [← hsplit, hfin, hpair]
  rw [hform, Complex.add_re, Complex.ofReal_re]
  have hre_le : (∑' x : ↑((↑T : Set Zero)ᶜ), hermTerm (anchor ρ.val.im σ₀) R x.val).re ≤ Ct :=
    (Complex.re_le_norm _).trans htail
  linarith [hzre, hkey, hre_le]

/-! ## The unconditional criterion -/

/-- **The prime-anchor seat criterion, unconditional in both directions.**  RH holds iff the
Hermitian form `Q_w(R) = Σ_ρ m_ρ conj(R(conj x_ρ)) R(x'_ρ)` — whose entries are absolutely
convergent, prime-computable Dirichlet series at anchors `1 < σ₀ < 3/2` — has nonnegative real
part at every such anchor along every polynomial `R` with `R(0) = 0`. -/
theorem rh_iff_hermForm_nonneg :
    (∀ ρ ∈ ZD.NontrivialZeros, ρ.re = 1 / 2) ↔
    (∀ γ σ₀ : ℝ, 1 < σ₀ → σ₀ < 3 / 2 → ∀ R : Polynomial ℂ, R.coeff 0 = 0 →
      0 ≤ (hermForm (anchor γ σ₀) R).re) := by
  constructor
  · intro hon γ σ₀ _ _ R _
    exact hermForm_re_nonneg_of_online R hon
  · intro hpos ρ hρ
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hoff : 1 / 2 < (feReflectZ ⟨ρ, hρ⟩).val.re := by
        rw [feReflectZ_val, feReflect_re]
        show 1 / 2 < 1 - ρ.re
        linarith
      obtain ⟨R, hR0, hneg⟩ :=
        exists_hermForm_neg hoff (σ₀ := 5 / 4) (by norm_num) (by norm_num)
      exact absurd (hpos _ _ (by norm_num) (by norm_num) R hR0) (not_le.mpr hneg)
    · obtain ⟨R, hR0, hneg⟩ :=
        exists_hermForm_neg (ρ := ⟨ρ, hρ⟩) hgt (σ₀ := 5 / 4) (by norm_num) (by norm_num)
      exact absurd (hpos _ _ (by norm_num) (by norm_num) R hR0) (not_le.mpr hneg)

end CriticalLinePhasor.SeatPrimeAnchorHermitian

#print axioms CriticalLinePhasor.SeatPrimeAnchorHermitian.hermForm_re_nonneg_of_online
#print axioms CriticalLinePhasor.SeatPrimeAnchorHermitian.exists_hermForm_neg
#print axioms CriticalLinePhasor.SeatPrimeAnchorHermitian.rh_iff_hermForm_nonneg
