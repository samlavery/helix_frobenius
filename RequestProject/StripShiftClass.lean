import RequestProject.DeBruijnStripStep
import RequestProject.HurwitzLimit

/-!
# The imaginary shift on real polynomials, and de Bruijn's strip class (T2c)

* `shiftPoly h p : ℝ[X]` — the real polynomial with `shiftPoly h p (z) = p(z + ih) + p(z − ih)`
  (obtained from the complex polynomial `p(X + ih) + p(X − ih)`, whose coefficients are real);
* `StripClass σ f` — `f` is a locally uniform limit on `ℂ` of nonzero real polynomials all of whose zeros
  satisfy `(Im w)² ≤ σ`;
* `StripClass.shift` — the class is closed under `f ↦ f(· + ih) + f(· − ih)`, the strip narrowing from `σ` to
  `max (σ − h²) 0` (the compiled polynomial step `polynomial_shift_zero_strip`);
* `StripClass.shiftIter` — `N` shifts narrow to `max (σ − N h²) 0`;
* `StripClass.im_eq_zero_of_zero` — a member of the class at `σ = 0`, not identically zero, has only real zeros
  (Hurwitz).
-/

open Complex Polynomial Filter Topology Set

namespace CriticalLinePhasor.DeBruijn

/-! ### The shifted polynomial -/

/-- The complex polynomial `p(X + ih) + p(X − ih)`. -/
noncomputable def shiftPolyC (h : ℝ) (p : ℝ[X]) : ℂ[X] :=
  (p.map (algebraMap ℝ ℂ)).comp (X + C (I * h)) + (p.map (algebraMap ℝ ℂ)).comp (X - C (I * h))

theorem aeval_eq_eval_map (p : ℝ[X]) (z : ℂ) : aeval z p = (p.map (algebraMap ℝ ℂ)).eval z := by
  rw [aeval_def, eval_map]

theorem shiftPolyC_eval (h : ℝ) (p : ℝ[X]) (z : ℂ) :
    (shiftPolyC h p).eval z = aeval (z + I * h) p + aeval (z - I * h) p := by
  simp only [shiftPolyC, eval_add, eval_comp, eval_X, eval_C, eval_sub, aeval_eq_eval_map]

theorem hasseDeriv_map_real (k : ℕ) (p : ℝ[X]) :
    hasseDeriv k (p.map (algebraMap ℝ ℂ)) = (hasseDeriv k p).map (algebraMap ℝ ℂ) := by
  ext n
  simp only [hasseDeriv_coeff, coeff_map, map_mul, map_natCast]

/-- The coefficients of `shiftPolyC h p` are real. -/
theorem shiftPolyC_coeff_real (h : ℝ) (p : ℝ[X]) (n : ℕ) :
    ((shiftPolyC h p).coeff n).im = 0 := by
  have hX : (X - C (I * h) : ℂ[X]) = X + C (-(I * h)) := by rw [C_neg, sub_eq_add_neg]
  simp only [shiftPolyC, coeff_add, ← taylor_apply, taylor_coeff, hX, hasseDeriv_map_real]
  set q := hasseDeriv n p
  have h1 : (q.map (algebraMap ℝ ℂ)).eval (I * h) = aeval (I * h) q := (aeval_eq_eval_map q _).symm
  have h2 : (q.map (algebraMap ℝ ℂ)).eval (-(I * h)) = aeval (-(I * h)) q := (aeval_eq_eval_map q _).symm
  rw [h1, h2]
  have hc : (-(I * h) : ℂ) = (starRingEnd ℂ) (I * h) := by simp
  rw [hc, Polynomial.aeval_conj, Complex.add_conj]
  simp

theorem shiftPolyC_mem_lifts (h : ℝ) (p : ℝ[X]) : shiftPolyC h p ∈ lifts (algebraMap ℝ ℂ) := by
  rw [lifts_iff_coeff_lifts]
  intro n
  refine ⟨((shiftPolyC h p).coeff n).re, ?_⟩
  have := shiftPolyC_coeff_real h p n
  apply Complex.ext <;> simp [this]

/-- **The real shifted polynomial** `shiftPoly h p`, with `aeval z (shiftPoly h p) = p(z + ih) + p(z − ih)`. -/
noncomputable def shiftPoly (h : ℝ) (p : ℝ[X]) : ℝ[X] :=
  Classical.choose ((mem_lifts _).mp (shiftPolyC_mem_lifts h p))

theorem shiftPoly_map (h : ℝ) (p : ℝ[X]) : (shiftPoly h p).map (algebraMap ℝ ℂ) = shiftPolyC h p :=
  Classical.choose_spec ((mem_lifts _).mp (shiftPolyC_mem_lifts h p))

theorem aeval_shiftPoly (h : ℝ) (p : ℝ[X]) (z : ℂ) :
    aeval z (shiftPoly h p) = aeval (z + I * h) p + aeval (z - I * h) p := by
  rw [aeval_eq_eval_map, shiftPoly_map, shiftPolyC_eval]

/-- A nonzero real polynomial with zeros in a strip has a nonzero shift (its shift would otherwise vanish
at a point far above the strip). -/
theorem shiftPoly_ne_zero {p : ℝ[X]} (hp : p ≠ 0) {h Δ : ℝ} (hh : 0 < h)
    (hstrip : ∀ w : ℂ, aeval w p = 0 → w.im ^ 2 ≤ Δ ^ 2) : shiftPoly h p ≠ 0 := by
  intro h0
  set w : ℂ := I * ((|Δ| + 1 : ℝ) : ℂ) with hw
  have hz : aeval (w + I * h) p + aeval (w - I * h) p = 0 := by
    rw [← aeval_shiftPoly, h0, map_zero]
  have him : w.im = |Δ| + 1 := by rw [hw]; simp
  rcases polynomial_shift_zero_strip p hp hh hstrip hz with h1 | h1
  · rw [him] at h1; linarith [abs_nonneg Δ]
  · rw [him] at h1
    nlinarith [abs_nonneg Δ, sq_abs Δ, sq_nonneg h]

/-! ### The strip class -/

/-- `f` is a locally uniform limit on `ℂ` of nonzero real polynomials whose zeros satisfy `(Im w)² ≤ σ`. -/
def StripClass (σ : ℝ) (f : ℂ → ℂ) : Prop :=
  ∃ P : ℕ → ℝ[X], (∀ n, P n ≠ 0) ∧ (∀ n (w : ℂ), aeval w (P n) = 0 → w.im ^ 2 ≤ σ) ∧
    TendstoLocallyUniformly (fun n z => aeval z (P n)) f atTop

/-- The shift operator `f ↦ f(· + ih) + f(· − ih)`. -/
noncomputable def shiftOp (h : ℝ) (f : ℂ → ℂ) : ℂ → ℂ := fun z => f (z + I * h) + f (z - I * h)

theorem StripClass.congr_σ {σ σ' : ℝ} (hσ : σ = σ') {f : ℂ → ℂ} (hf : StripClass σ f) : StripClass σ' f :=
  hσ ▸ hf

theorem differentiable_aeval (p : ℝ[X]) : Differentiable ℂ (fun z : ℂ => aeval z p) := by
  have : (fun z : ℂ => aeval z p) = fun z => (p.map (algebraMap ℝ ℂ)).eval z := by
    funext z; exact aeval_eq_eval_map p z
  rw [this]
  exact Polynomial.differentiable _

/-- Sums of locally uniform limits (on the locally compact `ℂ`). -/
theorem tendstoLocallyUniformly_add {F G : ℕ → ℂ → ℂ} {f g : ℂ → ℂ}
    (hF : TendstoLocallyUniformly F f atTop) (hG : TendstoLocallyUniformly G g atTop) :
    TendstoLocallyUniformly (fun n z => F n z + G n z) (fun z => f z + g z) atTop := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact] at hF hG ⊢
  intro K hK
  exact (hF K hK).add (hG K hK)

/-- **One shift narrows the strip:** `σ ↦ max (σ − h²) 0`. -/
theorem StripClass.shift {σ : ℝ} (hσ : 0 ≤ σ) {f : ℂ → ℂ} (hf : StripClass σ f) {h : ℝ} (hh : 0 < h) :
    StripClass (max (σ - h ^ 2) 0) (shiftOp h f) := by
  obtain ⟨P, hP0, hPz, hPlim⟩ := hf
  have hstrip : ∀ n (w : ℂ), aeval w (P n) = 0 → w.im ^ 2 ≤ (Real.sqrt σ) ^ 2 := by
    intro n w hw; rw [Real.sq_sqrt hσ]; exact hPz n w hw
  refine ⟨fun n => shiftPoly h (P n), fun n => shiftPoly_ne_zero (hP0 n) hh (hstrip n), ?_, ?_⟩
  · intro n w hw
    rw [aeval_shiftPoly] at hw
    rcases polynomial_shift_zero_strip (P n) (hP0 n) hh (hstrip n) hw with h1 | h1
    · rw [h1]; simp
    · rw [Real.sq_sqrt hσ] at h1
      exact le_max_of_le_left (by linarith)
  · have h1 := hPlim.comp (fun z : ℂ => z + I * h) (by fun_prop)
    have h2 := hPlim.comp (fun z : ℂ => z - I * h) (by fun_prop)
    have := tendstoLocallyUniformly_add h1 h2
    refine this.congr ?_ |>.congr_right ?_
    · intro n z
      simp only [Function.comp_apply, aeval_shiftPoly]
    · intro z; rfl

/-- **`N` shifts narrow the strip to `max (σ − N h²) 0`.** -/
theorem StripClass.shiftIter {σ : ℝ} (hσ : 0 ≤ σ) {f : ℂ → ℂ} (hf : StripClass σ f) {h : ℝ} (hh : 0 < h)
    (N : ℕ) : StripClass (max (σ - N * h ^ 2) 0) ((shiftOp h)^[N] f) := by
  induction N with
  | zero =>
    simp only [Function.iterate_zero, id_eq, Nat.cast_zero, zero_mul, sub_zero]
    exact hf.congr_σ (max_eq_left hσ).symm
  | succ N ih =>
    rw [Function.iterate_succ_apply']
    have := (ih.shift (le_max_right _ _) hh)
    refine this.congr_σ ?_
    push_cast
    rcases le_or_gt 0 (σ - N * h ^ 2) with h1 | h1
    · rw [max_eq_left h1]; ring_nf
    · rw [max_eq_right h1.le]
      have : σ - (N + 1) * h ^ 2 ≤ 0 := by nlinarith [sq_nonneg h]
      rw [max_eq_right this, max_eq_right (by nlinarith [sq_nonneg h])]

/-- **Real zeros at `σ = 0`:** a member of the class at `σ = 0`, not identically zero, has only real zeros. -/
theorem StripClass.im_eq_zero_of_zero {f : ℂ → ℂ} (hf : StripClass 0 f) (hne : ∃ z, f z ≠ 0) :
    ∀ z : ℂ, f z = 0 → z.im = 0 := by
  obtain ⟨P, hP0, hPz, hPlim⟩ := hf
  refine CriticalLinePhasor.Hurwitz.im_eq_zero_of_tendstoLocallyUniformly
    (fun n => differentiable_aeval (P n)) ?_ hPlim hne
  intro n z hz
  have := hPz n z hz
  nlinarith [sq_nonneg z.im]

end CriticalLinePhasor.DeBruijn

#print axioms CriticalLinePhasor.DeBruijn.aeval_shiftPoly
#print axioms CriticalLinePhasor.DeBruijn.StripClass.shift
#print axioms CriticalLinePhasor.DeBruijn.StripClass.shiftIter
#print axioms CriticalLinePhasor.DeBruijn.StripClass.im_eq_zero_of_zero
