import RequestProject.RealRootedDeriv

/-!
# `StripClass 0` is closed under differentiation

The Laguerre–Pólya class is closed under `d/dz`.  The only obstacle is witness bookkeeping: a witness
`P n` may be a nonzero CONSTANT, and then `derivative (P n) = 0` has every point as a "root".  That
can only happen finitely often once `deriv f ≢ 0`: convergence at a point where `deriv f ≠ 0` forces
`aeval z₀ (derivative (P n)) ≠ 0` eventually, hence `0 < (P n).natDegree` eventually.  Passing to that
tail (`tendstoLocallyUniformly_shift`) makes Hurwitz applicable.
-/

open Polynomial Complex Filter Topology

namespace CriticalLinePhasor.DeBruijn

/-- Locally uniform convergence is a tail property: shifting the index preserves it. -/
theorem tendstoLocallyUniformly_shift {F : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    (h : TendstoLocallyUniformly F g atTop) (N : ℕ) :
    TendstoLocallyUniformly (fun k => F (k + N)) g atTop := by
  intro u hu x
  obtain ⟨t, ht, htu⟩ := h u hu x
  exact ⟨t, ht, (tendsto_add_atTop_nat N).eventually htu⟩

/-- The derivative of the polynomial evaluation is the evaluation of the derivative. -/
theorem deriv_aeval_eq (p : ℝ[X]) :
    deriv (fun z : ℂ => aeval z p) = fun z : ℂ => aeval z (derivative p) := by
  funext z
  have h1 : (fun z : ℂ => aeval z p) = fun z : ℂ => Polynomial.eval z (p.map (algebraMap ℝ ℂ)) := by
    funext w; rw [aeval_eq_eval_map]
  rw [h1, Polynomial.deriv, Polynomial.derivative_map, ← aeval_eq_eval_map]

/-- **The Laguerre–Pólya class is closed under `deriv`**, in the form needed: if `f` is a locally
uniform limit of real polynomials with only real zeros and `deriv f` is not identically zero, then
`deriv f` has only real zeros. -/
theorem StripClass.deriv_im_zero {f : ℂ → ℂ} (hf : StripClass 0 f) (hne : ∃ z, deriv f z ≠ 0) :
    ∀ z : ℂ, deriv f z = 0 → z.im = 0 := by
  obtain ⟨P, hP0, hPz, hPlim⟩ := hf
  have hreal : ∀ n, ∀ w : ℂ, aeval w (P n) = 0 → w.im = 0 := by
    intro n w hw
    have := hPz n w hw
    nlinarith [sq_nonneg w.im]
  -- the derivatives converge to `deriv f`
  have hdconv : TendstoLocallyUniformly
      (fun n z => aeval z (derivative (P n))) (deriv f) atTop := by
    have hd := (hPlim.tendstoLocallyUniformlyOn (s := Set.univ)).deriv
      (Eventually.of_forall fun n => (differentiable_aeval (P n)).differentiableOn) isOpen_univ
    rw [tendstoLocallyUniformlyOn_univ] at hd
    have hfunseq : (deriv ∘ fun n (z : ℂ) => aeval z (P n))
        = fun n (z : ℂ) => aeval z (derivative (P n)) := by
      funext n
      exact deriv_aeval_eq (P n)
    rwa [hfunseq] at hd
  -- only finitely many witnesses can be constant
  obtain ⟨z₀, hz₀⟩ := hne
  have hptw : Tendsto (fun n => aeval z₀ (derivative (P n))) atTop (𝓝 (deriv f z₀)) :=
    (tendstoLocallyUniformlyOn_univ.mpr hdconv).tendsto_at (Set.mem_univ z₀)
  have hevne : ∀ᶠ n in atTop, aeval z₀ (derivative (P n)) ≠ 0 := hptw.eventually_ne hz₀
  obtain ⟨N, hN⟩ := eventually_atTop.mp hevne
  have hdeg : ∀ k : ℕ, 0 < (P (k + N)).natDegree := by
    intro k
    by_contra hc
    have h0 : (P (k + N)).natDegree = 0 := by omega
    have hz : derivative (P (k + N)) = 0 := by
      rw [Polynomial.eq_C_of_natDegree_eq_zero h0]; simp
    exact hN (k + N) (Nat.le_add_left _ _) (by rw [hz]; simp)
  -- Hurwitz on the tail
  refine CriticalLinePhasor.Hurwitz.im_eq_zero_of_tendstoLocallyUniformly
    (fun k => differentiable_aeval (derivative (P (k + N)))) ?_
    (tendstoLocallyUniformly_shift hdconv N) ⟨z₀, hz₀⟩
  intro k w hw
  exact derivative_im_zero (hdeg k) (hreal (k + N)) w hw


/-- **Membership form**, which is what iterating needs: `StripClass 0` is closed under `deriv`, not
merely "the derivative has real zeros".  The witnesses are the derivatives of the tail. -/
theorem StripClass.deriv_mem {f : ℂ → ℂ} (hf : StripClass 0 f) (hne : ∃ z, deriv f z ≠ 0) :
    StripClass 0 (deriv f) := by
  obtain ⟨P, hP0, hPz, hPlim⟩ := hf
  have hreal : ∀ n, ∀ w : ℂ, aeval w (P n) = 0 → w.im = 0 := by
    intro n w hw
    have := hPz n w hw
    nlinarith [sq_nonneg w.im]
  have hdconv : TendstoLocallyUniformly
      (fun n z => aeval z (derivative (P n))) (deriv f) atTop := by
    have hd := (hPlim.tendstoLocallyUniformlyOn (s := Set.univ)).deriv
      (Eventually.of_forall fun n => (differentiable_aeval (P n)).differentiableOn) isOpen_univ
    rw [tendstoLocallyUniformlyOn_univ] at hd
    have hfunseq : (deriv ∘ fun n (z : ℂ) => aeval z (P n))
        = fun n (z : ℂ) => aeval z (derivative (P n)) := by
      funext n
      exact deriv_aeval_eq (P n)
    rwa [hfunseq] at hd
  obtain ⟨z₀, hz₀⟩ := hne
  have hptw : Tendsto (fun n => aeval z₀ (derivative (P n))) atTop (𝓝 (deriv f z₀)) :=
    (tendstoLocallyUniformlyOn_univ.mpr hdconv).tendsto_at (Set.mem_univ z₀)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hptw.eventually_ne hz₀)
  have hdeg : ∀ k : ℕ, 0 < (P (k + N)).natDegree := by
    intro k
    by_contra hc
    have h0 : (P (k + N)).natDegree = 0 := by omega
    have hzz : derivative (P (k + N)) = 0 := by
      rw [Polynomial.eq_C_of_natDegree_eq_zero h0]; simp
    exact hN (k + N) (Nat.le_add_left _ _) (by rw [hzz]; simp)
  refine ⟨fun k => derivative (P (k + N)), ?_, ?_, tendstoLocallyUniformly_shift hdconv N⟩
  · intro k h0
    exact (Polynomial.derivative_ne_zero.mpr (by have := hdeg k; omega)) h0
  · intro k w hw
    have := derivative_im_zero (hdeg k) (hreal (k + N)) w hw
    simp [this]


/-- If `deriv^[k] f` is not identically zero, neither is any earlier derivative. -/
theorem iterate_deriv_ne_zero_of_succ {f : ℂ → ℂ} {k : ℕ} (h : ∃ z, deriv^[k + 1] f z ≠ 0) :
    ∃ z, deriv^[k] f z ≠ 0 := by
  by_contra hc
  push_neg at hc
  obtain ⟨z, hz⟩ := h
  apply hz
  have hfun : deriv^[k] f = 0 := funext hc
  rw [Function.iterate_succ_apply', hfun]
  simp

/-- **`StripClass 0` is closed under every iterate of `deriv`**, given only that the top iterate is
not identically zero — which supplies all the intermediate non-vanishing. -/
theorem StripClass.iterate_deriv_mem : ∀ (k : ℕ) {f : ℂ → ℂ}, StripClass 0 f →
    (∃ z, deriv^[k] f z ≠ 0) → StripClass 0 (deriv^[k] f) := by
  intro k
  induction k with
  | zero => intro f hf _; simpa using hf
  | succ k ih =>
    intro f hf hne
    have hk : ∃ z, deriv^[k] f z ≠ 0 := iterate_deriv_ne_zero_of_succ hne
    have hmem := ih hf hk
    rw [Function.iterate_succ_apply'] at hne ⊢
    exact hmem.deriv_mem hne

end CriticalLinePhasor.DeBruijn

#print axioms CriticalLinePhasor.DeBruijn.tendstoLocallyUniformly_shift
#print axioms CriticalLinePhasor.DeBruijn.StripClass.deriv_im_zero
#print axioms CriticalLinePhasor.DeBruijn.StripClass.deriv_mem
#print axioms CriticalLinePhasor.DeBruijn.StripClass.iterate_deriv_mem
