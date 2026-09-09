import Mathlib

set_option autoImplicit false

open Complex
open scoped ComplexConjugate
open scoped BigOperators

namespace CriticalLinePhasor.DeBruijn

/-- The real quadratic with conjugate roots `a ± I * b`. -/
noncomputable def pairFactor (a b : ℝ) (z : ℂ) : ℂ := (z - a) ^ 2 + (b : ℂ) ^ 2

theorem pairFactor_normSq_shift (a b h : ℝ) (z : ℂ) :
    normSq (pairFactor a b (z + I * h)) -
        normSq (pairFactor a b (z - I * h)) =
      8 * z.im * h * ((z.re - a) ^ 2 + z.im ^ 2 + h ^ 2 - b ^ 2) := by
  simp only [pairFactor, normSq_apply, add_re, add_im, sub_re, sub_im,
    mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im, pow_two]
  ring

theorem pairFactor_norm_shift_lt {a b h : ℝ} {z : ℂ}
    (hy : 0 < z.im) (hh : 0 < h) (hb : b ^ 2 < z.im ^ 2 + h ^ 2) :
    ‖pairFactor a b (z - I * h)‖ < ‖pairFactor a b (z + I * h)‖ := by
  have hpos : 0 < 8 * z.im * h * ((z.re - a) ^ 2 + z.im ^ 2 + h ^ 2 - b ^ 2) :=
    mul_pos (mul_pos (mul_pos (by norm_num) hy) hh) (by nlinarith [sq_nonneg (z.re - a)])
  rw [← pairFactor_normSq_shift, normSq_eq_norm_sq, normSq_eq_norm_sq] at hpos
  nlinarith [norm_nonneg (pairFactor a b (z - I * h)),
    norm_nonneg (pairFactor a b (z + I * h))]

theorem pairFactor_conj (a b : ℝ) (z : ℂ) :
    pairFactor a b (conj z) = conj (pairFactor a b z) := by
  simp [pairFactor]

theorem pairFactor_eq_mul (w z : ℂ) :
    pairFactor w.re w.im z = (z - w) * (z - conj w) := by
  apply Complex.ext <;>
    simp [pairFactor, pow_two, Complex.mul_re, Complex.mul_im] <;> ring

/-- Squaring a real polynomial pairs every root with its conjugate without
choosing or discarding any root; all multiplicities are retained. -/
theorem polynomial_sq_eq_pair_product (p : Polynomial ℝ) (z : ℂ) :
    (p.aeval z) ^ 2 = (p.leadingCoeff : ℂ) ^ 2 *
      ((p.aroots ℂ).map (fun w => pairFactor w.re w.im z)).prod := by
  have hs := IsAlgClosed.splits (p.map (algebraMap ℝ ℂ))
  calc
    (p.aeval z) ^ 2 = p.aeval z * conj (p.aeval (conj z)) := by
      rw [Polynomial.aeval_conj, Complex.conj_conj, pow_two]
    _ = (p.leadingCoeff : ℂ) ^ 2 *
        ((p.aroots ℂ).map (fun w => pairFactor w.re w.im z)).prod := by
      rw [hs.aeval_eq_prod_aroots z, hs.aeval_eq_prod_aroots (conj z)]
      change (p.leadingCoeff : ℂ) * _ * conj ((p.leadingCoeff : ℂ) * _) = _
      simp only [map_mul, Complex.conj_ofReal,
        map_multiset_prod, Multiset.map_map, Function.comp_apply, map_sub,
        Complex.conj_conj, pairFactor_eq_mul, Multiset.prod_map_mul]
      ring

theorem polynomial_norm_sq_eq_pair_product (p : Polynomial ℝ) (z : ℂ) :
    ‖p.aeval z‖ ^ 2 = ‖(p.leadingCoeff : ℂ)‖ ^ 2 *
      ((p.aroots ℂ).map (fun w => ‖pairFactor w.re w.im z‖)).prod := by
  have heq := congrArg norm (polynomial_sq_eq_pair_product p z)
  rw [norm_pow, norm_mul, norm_pow] at heq
  rw [show ‖((p.aroots ℂ).map (fun w => pairFactor w.re w.im z)).prod‖ =
      ((p.aroots ℂ).map (fun w => ‖pairFactor w.re w.im z‖)).prod from by
    simpa [Multiset.map_map, Function.comp_apply, _root_.normHom] using
      (map_multiset_prod (_root_.normHom : ℂ →*₀ ℝ)
        ((p.aroots ℂ).map (fun w => pairFactor w.re w.im z)))] at heq
  exact heq

private theorem multiset_prod_strict {ι : Type*} (s : Multiset ι) (f g : ι → ℝ)
    (hs : s ≠ 0) (hf : ∀ i ∈ s, 0 ≤ f i) (hfg : ∀ i ∈ s, f i < g i) :
    (s.map f).prod < (s.map g).prod := by
  induction s using Multiset.induction_on with
  | empty => exact (hs rfl).elim
  | @cons i s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons]
    have hi := hfg i (Multiset.mem_cons_self _ _)
    have hfi := hf i (Multiset.mem_cons_self _ _)
    by_cases hs' : s = 0
    · subst s; simpa using hi
    · have ht := ih hs' (fun j hj => hf j (Multiset.mem_cons_of_mem hj))
        (fun j hj => hfg j (Multiset.mem_cons_of_mem hj))
      have hp : 0 ≤ (s.map f).prod := Multiset.prod_nonneg (by
        intro x hx
        obtain ⟨j, hj, rfl⟩ := Multiset.mem_map.mp hx
        exact hf j (Multiset.mem_cons_of_mem hj))
      exact (mul_le_mul_of_nonneg_right hi.le hp).trans_lt
        (mul_lt_mul_of_pos_left ht (hfi.trans_lt hi))

theorem polynomial_norm_shift_lt (p : Polynomial ℝ) (hp : p ≠ 0)
    (hroots : p.aroots ℂ ≠ 0) {h Δ : ℝ} {z : ℂ} (hy : 0 < z.im) (hh : 0 < h)
    (hb : ∀ w ∈ p.aroots ℂ, w.im ^ 2 ≤ Δ ^ 2)
    (hout : Δ ^ 2 < z.im ^ 2 + h ^ 2) :
    ‖p.aeval (z - I * h)‖ < ‖p.aeval (z + I * h)‖ := by
  have ht := multiset_prod_strict (p.aroots ℂ)
    (fun w => ‖pairFactor w.re w.im (z - I * h)‖)
    (fun w => ‖pairFactor w.re w.im (z + I * h)‖) hroots
    (fun _ _ => norm_nonneg _)
    (fun w hw => pairFactor_norm_shift_lt hy hh ((hb w hw).trans_lt hout))
  have hc : 0 < ‖(p.leadingCoeff : ℂ)‖ ^ 2 := by
    apply sq_pos_of_pos
    exact norm_pos_iff.mpr (Complex.ofReal_ne_zero.mpr (Polynomial.leadingCoeff_ne_zero.mpr hp))
  have heq := mul_lt_mul_of_pos_left ht hc
  rw [← polynomial_norm_sq_eq_pair_product, ← polynomial_norm_sq_eq_pair_product] at heq
  nlinarith [norm_nonneg (p.aeval (z - I * h)), norm_nonneg (p.aeval (z + I * h))]

/-- The polynomial strip-narrowing step, with no simplicity assumption. -/
theorem polynomial_shift_zero_strip (p : Polynomial ℝ) (hp : p ≠ 0)
    {h Δ : ℝ} (hh : 0 < h)
    (hstrip : ∀ w : ℂ, p.aeval w = 0 → w.im ^ 2 ≤ Δ ^ 2) {z : ℂ}
    (hz : p.aeval (z + I * h) + p.aeval (z - I * h) = 0) :
    z.im = 0 ∨ z.im ^ 2 + h ^ 2 ≤ Δ ^ 2 := by
  by_cases hroots : p.aroots ℂ = 0
  · have hs := IsAlgClosed.splits (p.map (algebraMap ℝ ℂ))
    rw [hs.aeval_eq_prod_aroots, hs.aeval_eq_prod_aroots, hroots] at hz
    simp only [Multiset.map_zero, Multiset.prod_zero, mul_one] at hz
    have hc : (p.leadingCoeff : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Polynomial.leadingCoeff_ne_zero.mpr hp)
    exfalso
    apply hc
    change (p.leadingCoeff : ℂ) + (p.leadingCoeff : ℂ) = 0 at hz
    linear_combination hz / 2
  · have hb : ∀ w ∈ p.aroots ℂ, w.im ^ 2 ≤ Δ ^ 2 :=
      fun w hw => hstrip w (Polynomial.mem_aroots.mp hw).2
    have upper : ∀ w : ℂ, 0 < w.im →
        p.aeval (w + I * h) + p.aeval (w - I * h) = 0 →
        w.im ^ 2 + h ^ 2 ≤ Δ ^ 2 := by
      intro w hw hwzero
      by_contra! hout
      have hlt := polynomial_norm_shift_lt p hp hroots hw hh hb hout
      have heq := congrArg norm (eq_neg_of_add_eq_zero_left hwzero)
      rw [norm_neg] at heq
      exact (ne_of_lt hlt) heq.symm
    rcases lt_trichotomy 0 z.im with hy | hy | hy
    · exact Or.inr (upper z hy hz)
    · exact Or.inl hy.symm
    · right
      have hc : p.aeval (conj z + I * h) + p.aeval (conj z - I * h) = 0 := by
        have hp' : conj z + I * h = conj (z - I * h) := by simp
        have hm : conj z - I * h = conj (z + I * h) := by simp [sub_eq_add_neg]
        rw [hp', hm, Polynomial.aeval_conj, Polynomial.aeval_conj,
          ← map_add, add_comm, hz, map_zero]
      simpa using upper (conj z) (by simpa using neg_pos.mpr hy) hc

theorem polynomial_shift_real_zeros (p : Polynomial ℝ) (hp : p ≠ 0)
    {h Δ : ℝ} (hh : 0 < h)
    (hstrip : ∀ w : ℂ, p.aeval w = 0 → w.im ^ 2 ≤ Δ ^ 2)
    (hwidth : Δ ^ 2 ≤ h ^ 2) {z : ℂ}
    (hz : p.aeval (z + I * h) + p.aeval (z - I * h) = 0) : z.im = 0 := by
  rcases polynomial_shift_zero_strip p hp hh hstrip hz with heq | hle
  · exact heq
  · nlinarith [sq_nonneg z.im]

/-- A product of conjugate-root quadratics; repeated indices retain multiplicity. -/
noncomputable def pairProduct {ι : Type*} (s : Finset ι) (a b : ι → ℝ) (z : ℂ) : ℂ :=
  ∏ i ∈ s, pairFactor (a i) (b i) z

theorem pairProduct_norm_shift_lt {ι : Type*} {s : Finset ι} {a b : ι → ℝ}
    {h Δ : ℝ} {z : ℂ} (hs : s.Nonempty) (hy : 0 < z.im) (hh : 0 < h)
    (hb : ∀ i ∈ s, (b i) ^ 2 ≤ Δ ^ 2) (hout : Δ ^ 2 < z.im ^ 2 + h ^ 2) :
    ‖pairProduct s a b (z - I * h)‖ < ‖pairProduct s a b (z + I * h)‖ := by
  classical
  simp only [pairProduct, norm_prod]
  induction s using Finset.induction_on with
  | empty => simp at hs
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    have hi' := pairFactor_norm_shift_lt (a := a i) hy hh
      ((hb i (Finset.mem_insert_self _ _)).trans_lt hout)
    by_cases hs' : s.Nonempty
    · have htail := ih hs' (fun j hj => hb j (Finset.mem_insert_of_mem hj))
      exact (mul_le_mul_of_nonneg_right hi'.le
        (Finset.prod_nonneg (fun j _ => norm_nonneg _))).trans_lt
        (mul_lt_mul_of_pos_left htail (lt_of_le_of_lt (norm_nonneg _) hi'))
    · rw [Finset.not_nonempty_iff_eq_empty.mp hs']
      simpa using hi'

theorem pairProduct_conj {ι : Type*} (s : Finset ι) (a b : ι → ℝ) (z : ℂ) :
    pairProduct s a b (conj z) = conj (pairProduct s a b z) := by
  simp [pairProduct, pairFactor_conj]

/-- One symmetric imaginary-shift step. The two summands cannot cancel outside
the narrower strip, including when the product has repeated roots. -/
theorem pairProduct_shift_zero_strip {ι : Type*} (s : Finset ι) (a b : ι → ℝ)
    {h Δ : ℝ} (hh : 0 < h) (hb : ∀ i ∈ s, (b i) ^ 2 ≤ Δ ^ 2) {z : ℂ}
    (hz : pairProduct s a b (z + I * h) + pairProduct s a b (z - I * h) = 0) :
    z.im = 0 ∨ z.im ^ 2 + h ^ 2 ≤ Δ ^ 2 := by
  classical
  by_cases hs : s.Nonempty
  · have upper : ∀ w : ℂ, 0 < w.im →
        pairProduct s a b (w + I * h) + pairProduct s a b (w - I * h) = 0 →
        w.im ^ 2 + h ^ 2 ≤ Δ ^ 2 := by
      intro w hw hwzero
      by_contra! hout
      have hlt := pairProduct_norm_shift_lt (a := a) hs hw hh hb hout
      have heq := congrArg norm (eq_neg_of_add_eq_zero_left hwzero)
      rw [norm_neg] at heq
      exact (ne_of_lt hlt) heq.symm
    rcases lt_trichotomy 0 z.im with hy | hy | hy
    · exact Or.inr (upper z hy hz)
    · exact Or.inl hy.symm
    · right
      have hc : pairProduct s a b (conj z + I * h) +
          pairProduct s a b (conj z - I * h) = 0 := by
        have hp : conj z + I * h = conj (z - I * h) := by simp
        have hm : conj z - I * h = conj (z + I * h) := by simp [sub_eq_add_neg]
        rw [hp, hm, pairProduct_conj, pairProduct_conj, ← map_add, add_comm, hz, map_zero]
      simpa using upper (conj z) (by simpa using neg_pos.mpr hy) hc
  · have hs' := Finset.not_nonempty_iff_eq_empty.mp hs
    simp [hs', pairProduct] at hz

theorem pairProduct_shift_real_zeros {ι : Type*} (s : Finset ι) (a b : ι → ℝ)
    {h Δ : ℝ} (hh : 0 < h) (hb : ∀ i ∈ s, (b i) ^ 2 ≤ Δ ^ 2)
    (hwidth : Δ ^ 2 ≤ h ^ 2) {z : ℂ}
    (hz : pairProduct s a b (z + I * h) + pairProduct s a b (z - I * h) = 0) :
    z.im = 0 := by
  rcases pairProduct_shift_zero_strip s a b hh hb hz with h | h
  · exact h
  · nlinarith [sq_nonneg z.im]

end CriticalLinePhasor.DeBruijn

#print axioms CriticalLinePhasor.DeBruijn.pairFactor_normSq_shift
#print axioms CriticalLinePhasor.DeBruijn.pairFactor_norm_shift_lt
#print axioms CriticalLinePhasor.DeBruijn.pairProduct_norm_shift_lt
#print axioms CriticalLinePhasor.DeBruijn.pairProduct_shift_zero_strip
#print axioms CriticalLinePhasor.DeBruijn.pairProduct_shift_real_zeros
#print axioms CriticalLinePhasor.DeBruijn.polynomial_sq_eq_pair_product
#print axioms CriticalLinePhasor.DeBruijn.polynomial_shift_zero_strip
#print axioms CriticalLinePhasor.DeBruijn.polynomial_shift_real_zeros
