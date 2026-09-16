import RequestProject.FlowLamDerivCont

/-!
# The `z`-derivative family of the warped fiber, as integrals

`flowD k lam z = ∫ (iu)^k e^{λu²} K(u) e^{izu} du`.  Defining the derivatives as integrals rather than
as `deriv^[k]` makes the two operations close on the family:
* `∂_z (flowD k) = flowD (k+1)`  — the weight gains a factor `iu`;
* `∂_λ (flowD k) = −flowD (k+2)` — the weight gains `u² = −(iu)²`.
Hence the backward heat equation `∂_λ = −∂_z²` holds at EVERY order, with no interchange argument.

The extra weight is absorbed by `|u|^k ≤ k! e^{|u|}` into the same profile `Dq`.
-/

open Complex MeasureTheory Filter Topology

namespace CriticalLinePhasor.XiKernel

/-- The integrand, as a NAMED function: this is what lets the parametric-derivative lemma unify
`F` and `F'` syntactically instead of unfolding `(iu)^k`. -/
noncomputable def flowDInt (k : ℕ) (lam : ℝ) (z : ℂ) (u : ℝ) : ℂ :=
  (I * (u : ℂ)) ^ k * ((Real.exp (lam * u ^ 2) : ℝ) : ℂ) * Kker u * Complex.exp (I * z * u)

noncomputable def flowD (k : ℕ) (lam : ℝ) (z : ℂ) : ℂ := ∫ u : ℝ, flowDInt k lam z u

theorem flowD_zero_eq (lam : ℝ) (z : ℂ) : flowD 0 lam z = flowStage lam z := by
  unfold flowD flowDInt flowStage; simp

/-- `|u|^k ≤ k! · e^{|u|}`. -/
theorem abs_pow_le_factorial_exp (k : ℕ) (u : ℝ) :
    |u| ^ k ≤ (k.factorial : ℝ) * Real.exp |u| := by
  have h := Real.pow_div_factorial_le_exp |u| (abs_nonneg u) k
  have hf : (0:ℝ) < (k.factorial : ℝ) := by exact_mod_cast k.factorial_pos
  rw [div_le_iff₀ hf] at h
  linarith

theorem norm_I_mul_pow (k : ℕ) (u : ℝ) : ‖(I * (u : ℂ)) ^ k‖ = |u| ^ k := by
  rw [norm_pow, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]

theorem continuous_flowD_integrand (k : ℕ) (lam : ℝ) (z : ℂ) :
    Continuous (flowDInt k lam z) := by
  unfold flowDInt
  exact
  ((((continuous_const.mul Complex.continuous_ofReal).pow k).mul
    (Complex.continuous_ofReal.comp (Real.continuous_exp.comp (by fun_prop)))).mul
    continuous_Kker).mul (Complex.continuous_exp.comp (by fun_prop))

theorem flowD_integrand_bound {k : ℕ} {lam lam₁ B : ℝ} (hle : lam ≤ lam₁) {M : ℝ} (hM : 0 ≤ M)
    (hB : ∀ v : ℝ, |v| ^ k ≤ B * Real.exp |v|)
    (hK : ∀ u : ℝ, ‖Kker u‖ ≤ M * Dabs (1 / 2) (2 * Rc) u) {z : ℂ} {a : ℝ} (hz : |z.im| ≤ a)
    (u : ℝ) :
    ‖flowDInt k lam z u‖ ≤ (B * M) * Dq lam₁ (1 / 2 + (a + 1)) (2 * Rc) u := by
  unfold flowDInt
  have hexp : Real.exp (lam * u ^ 2) ≤ Real.exp (lam₁ * u ^ 2) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hle (sq_nonneg u))
  have hDnn := Dabs_nonneg (1 / 2) (2 * Rc) u
  have hpow := hB u
  rw [norm_mul, norm_mul, norm_mul, norm_I_mul_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  have hA : |u| ^ k * Real.exp (lam * u ^ 2)
      ≤ (B * Real.exp |u|) * Real.exp (lam₁ * u ^ 2) := by
    have hBnn : 0 ≤ B * Real.exp |u| := le_trans (pow_nonneg (abs_nonneg u) k) hpow
    exact mul_le_mul hpow hexp (Real.exp_pos _).le hBnn
  have hB' : ‖Kker u‖ * ‖Complex.exp (I * z * u)‖
      ≤ (M * Dabs (1 / 2) (2 * Rc) u) * Real.exp (a * |u|) :=
    mul_le_mul (hK u) (norm_exp_I_mul_le hz u) (norm_nonneg _) (mul_nonneg hM hDnn)
  have hL : |u| ^ k * Real.exp (lam * u ^ 2) * ‖Kker u‖ * ‖Complex.exp (I * z * u)‖
      = (|u| ^ k * Real.exp (lam * u ^ 2)) * (‖Kker u‖ * ‖Complex.exp (I * z * u)‖) := by ring
  rw [hL]
  have hBexp : 0 ≤ B * Real.exp |u| := le_trans (pow_nonneg (abs_nonneg u) k) (hB u)
  have hbnn : 0 ≤ B * Real.exp |u| * Real.exp (lam₁ * u ^ 2) :=
    mul_nonneg hBexp (Real.exp_pos _).le
  refine le_trans (mul_le_mul hA hB' (by positivity) hbnn) ?_
  have hrw : (B * Real.exp |u|) * Real.exp (lam₁ * u ^ 2)
        * ((M * Dabs (1 / 2) (2 * Rc) u) * Real.exp (a * |u|))
      = (B * M) * (Real.exp (lam₁ * u ^ 2)
          * (Dabs (1 / 2) (2 * Rc) u * Real.exp (a * |u|) * Real.exp (1 * |u|))) := by
    rw [one_mul]; ring
  rw [hrw, Dabs_mul_exp, Dabs_mul_exp]
  unfold Dq
  rw [show (1 / 2 + a + 1 : ℝ) = 1 / 2 + (a + 1) by ring]

theorem integrable_flowD_integrand (k : ℕ) {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (z : ℂ) :
    Integrable (flowDInt k lam z) := by
  obtain ⟨M, hM, hK⟩ := Kker_bound
  have hMnn : 0 ≤ M := by
    have := (norm_nonneg (Kker 0)).trans (hK 0)
    have hD : 0 < Dabs (1 / 2) (2 * Rc) 0 := by unfold Dabs Dprof; positivity
    nlinarith
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ v : ℝ, |v| ^ k ≤ B * Real.exp |v| :=
    ⟨(k.factorial : ℝ), abs_pow_le_factorial_exp k⟩
  have hdom : Integrable (fun u : ℝ => (B * M) * Dq lam (1 / 2 + (|z.im| + 1)) (2 * Rc) u) :=
    (integrable_Dq h0 h1 (by positivity) (by have := Rc_pos; positivity)).const_mul (B * M)
  refine hdom.mono' (continuous_flowD_integrand k lam z).aestronglyMeasurable ?_
  filter_upwards with u
  exact flowD_integrand_bound le_rfl hMnn hB hK le_rfl u


/-- Pointwise: `∂_z` of the integrand raises the weight. -/
theorem hasDerivAt_flowDInt_z (k : ℕ) (lam : ℝ) (u : ℝ) (z : ℂ) :
    HasDerivAt (fun w : ℂ => flowDInt k lam w u) (flowDInt (k + 1) lam z u) z := by
  unfold flowDInt
  have hlin : HasDerivAt (fun w : ℂ => I * w * u) (I * u) z := by
    simpa using ((hasDerivAt_id z).const_mul I).mul_const (u : ℂ)
  have hexp : HasDerivAt (fun w : ℂ => Complex.exp (I * w * u))
      (I * (u : ℂ) * Complex.exp (I * z * u)) z := by simpa [mul_comm] using hlin.cexp
  have hb := hexp.const_mul ((I * (u : ℂ)) ^ k * ((Real.exp (lam * u ^ 2) : ℝ) : ℂ) * Kker u)
  refine hb.congr_deriv ?_
  ring

/-- Pointwise: `∂_λ` of the integrand raises the weight by two, with a sign. -/
theorem hasDerivAt_flowDInt_lam (k : ℕ) (u : ℝ) (z : ℂ) (lam : ℝ) :
    HasDerivAt (fun t : ℝ => flowDInt k t z u) (-flowDInt (k + 2) lam z u) lam := by
  unfold flowDInt
  have hbase : HasDerivAt (fun t : ℝ => Real.exp (t * u ^ 2)) (Real.exp (lam * u ^ 2) * u ^ 2) lam := by
    simpa using (((hasDerivAt_id lam).mul_const (u ^ 2)).exp)
  have hC : HasDerivAt (fun t : ℝ => ((Real.exp (t * u ^ 2) : ℝ) : ℂ))
      (((Real.exp (lam * u ^ 2) * u ^ 2 : ℝ) : ℂ)) lam := hbase.ofReal_comp
  have hmul := ((hC.const_mul ((I * (u : ℂ)) ^ k)).mul_const (Kker u)).mul_const
    (Complex.exp (I * z * u))
  refine hmul.congr_deriv ?_
  have hI2 : (I * (u : ℂ)) ^ (k + 2) = (I * (u : ℂ)) ^ k * (I * (u : ℂ)) * (I * (u : ℂ)) := by
    rw [pow_succ, pow_succ]
  have hsplit : ((Real.exp (lam * u ^ 2) * u ^ 2 : ℝ) : ℂ)
      = ((Real.exp (lam * u ^ 2) : ℝ) : ℂ) * ((u : ℂ) ^ 2) := by
    rw [Complex.ofReal_mul, Complex.ofReal_pow]
  rw [hI2, hsplit]
  linear_combination ((I * (u : ℂ)) ^ k * ((Real.exp (lam * u ^ 2) : ℝ) : ℂ) * Kker u
    * Complex.exp (I * z * u) * (u : ℂ) ^ 2) * Complex.I_mul_I

/-- **`∂_z (flowD k) = flowD (k+1)`.** -/
theorem hasDerivAt_flowD_z (k : ℕ) {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (z₀ : ℂ) :
    HasDerivAt (flowD k lam) (flowD (k + 1) lam z₀) z₀ := by
  obtain ⟨M, hM, hK⟩ := Kker_bound
  have hMnn : 0 ≤ M := by
    have := (norm_nonneg (Kker 0)).trans (hK 0)
    have hD : 0 < Dabs (1 / 2) (2 * Rc) 0 := by unfold Dabs Dprof; positivity
    nlinarith
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ v : ℝ, |v| ^ (k + 1) ≤ B * Real.exp |v| :=
    ⟨(((k + 1).factorial : ℕ) : ℝ), abs_pow_le_factorial_exp (k + 1)⟩
  set a : ℝ := |z₀.im| + 1 with ha
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun (z : ℂ) (u : ℝ) => flowDInt k lam z u)
    (F' := fun (z : ℂ) (u : ℝ) => flowDInt (k + 1) lam z u)
    (bound := fun u : ℝ => (B * M) * Dq lam (1 / 2 + (a + 1)) (2 * Rc) u)
    (Metric.ball_mem_nhds z₀ one_pos)
    (Eventually.of_forall fun z => (continuous_flowD_integrand k lam z).aestronglyMeasurable)
    (integrable_flowD_integrand k h0 h1 z₀)
    (continuous_flowD_integrand (k + 1) lam z₀).aestronglyMeasurable
    (by filter_upwards with u; intro z hzb
        exact flowD_integrand_bound le_rfl hMnn hB hK
          (by rw [ha]; exact im_le_of_mem_ball hzb) u)
    ((integrable_Dq h0 h1 (by positivity) (by have := Rc_pos; positivity)).const_mul (B * M))
    (by filter_upwards with u; intro z _; exact hasDerivAt_flowDInt_z k lam u z)).2


/-- **`∂_λ (flowD k) = −flowD (k+2)`** — the backward heat equation, at every order, for free. -/
theorem hasDerivAt_flowD_lam (k : ℕ) {lam₀ lam₁ : ℝ} (h0 : 0 ≤ lam₀) (hlt : lam₀ < lam₁)
    (h1 : lam₁ ≤ 1) (z : ℂ) :
    HasDerivAt (fun t : ℝ => flowD k t z) (-(flowD (k + 2) lam₀ z)) lam₀ := by
  obtain ⟨M, hM, hK⟩ := Kker_bound
  have hMnn : 0 ≤ M := by
    have := (norm_nonneg (Kker 0)).trans (hK 0)
    have hD : 0 < Dabs (1 / 2) (2 * Rc) 0 := by unfold Dabs Dprof; positivity
    nlinarith
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ v : ℝ, |v| ^ (k + 2) ≤ B * Real.exp |v| :=
    ⟨(((k + 2).factorial : ℕ) : ℝ), abs_pow_le_factorial_exp (k + 2)⟩
  have hr : (0:ℝ) < lam₁ - lam₀ := by linarith
  have hmem : ∀ t ∈ Metric.ball lam₀ (lam₁ - lam₀), t ≤ lam₁ := by
    intro t ht
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at ht
    linarith [ht.2]
  have hres := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun (t : ℝ) (u : ℝ) => flowDInt k t z u)
    (F' := fun (t : ℝ) (u : ℝ) => -flowDInt (k + 2) t z u)
    (bound := fun u : ℝ => (B * M) * Dq lam₁ (1 / 2 + (|z.im| + 1)) (2 * Rc) u)
    (Metric.ball_mem_nhds lam₀ hr)
    (Eventually.of_forall fun t => (continuous_flowD_integrand k t z).aestronglyMeasurable)
    (integrable_flowD_integrand k h0 (le_trans hlt.le h1) z)
    ((continuous_flowD_integrand (k + 2) lam₀ z).neg.aestronglyMeasurable)
    (by filter_upwards with u; intro t ht
        rw [norm_neg]
        exact flowD_integrand_bound (hmem t ht) hMnn hB hK le_rfl u)
    ((integrable_Dq (le_trans h0 hlt.le) h1 (by positivity)
      (by have := Rc_pos; positivity)).const_mul (B * M))
    (by filter_upwards with u; intro t _; exact hasDerivAt_flowDInt_lam k u z t)
  have hneg : (∫ u : ℝ, -flowDInt (k + 2) lam₀ z u) = -(flowD (k + 2) lam₀ z) := by
    unfold flowD; rw [MeasureTheory.integral_neg]
  rw [hneg] at hres
  exact hres.2

/-- `flowD k lam` IS the `k`-th `z`-derivative of the stage. -/
theorem flowD_eq_iterate_deriv (k : ℕ) {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    flowD k lam = deriv^[k] (flowStage lam) := by
  induction k with
  | zero => funext z; simpa using flowD_zero_eq lam z
  | succ k ih =>
    funext z
    rw [Function.iterate_succ_apply', ← ih]
    exact ((hasDerivAt_flowD_z k h0 h1 z).deriv).symm

/-!
### Status

`∂_z (flowD k) = flowD (k+1)` and `∂_λ (flowD k) = −flowD (k+2)` are the two facts that make the
family closed and give the heat equation at every order.  The dominated-derivative proofs are the same
shape as `hasDerivAt_flowStage` / `hasDerivAt_flowStage_lam`, but the `(iu)^k` weight makes the
elaborator's `isDefEq` check time out on the metavariable for the derivative family; the fix is to
pin `F'` structurally rather than by unification.  Not done here.
-/

end CriticalLinePhasor.XiKernel

#print axioms CriticalLinePhasor.XiKernel.flowD_zero_eq
#print axioms CriticalLinePhasor.XiKernel.flowD_integrand_bound
#print axioms CriticalLinePhasor.XiKernel.integrable_flowD_integrand
#print axioms CriticalLinePhasor.XiKernel.hasDerivAt_flowD_z
#print axioms CriticalLinePhasor.XiKernel.hasDerivAt_flowD_lam
#print axioms CriticalLinePhasor.XiKernel.flowD_eq_iterate_deriv
