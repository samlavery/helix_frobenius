import Mathlib

/-!
# The sign–order transform

Ported from the house computation `tmp/rung3_lhs.py::sign_bit_from_order` (Sam's request,
2026-07-04).  That routine reads the **SIGN bit** of the weight-1 exotic `A₄` form's Frobenius
coefficient `a_p = ζ₁₂^{k(p)}` — the `k` vs `k+6` ambiguity, i.e. the `μ₁₂` vs `μ₆` (`±`) datum
that a character cannot see — from the **order of `Frob_p` in the double cover `2T = SL(2,3)`**:

  order 3  (8 factors of degree 3 mod `p`)  ⇒  sign `+1`;
  order 6  (4 factors of degree 6 mod `p`)  ⇒  sign `−1`.

The group-theoretic content, formalized here, is a general fact about a **double cover**
(central extension by an order-2 element `z`): a lift `g` of an element of order `d` in the
base has order `d` or `2d`, and the order **reads the sign** (which of the two preimages `±g`):

* `orderOf_eq_of_sign_pos`      — sign `+1` (`g^d = 1`)  ⇒  `orderOf g = d`;
* `orderOf_eq_two_mul_of_sign_neg` — sign `−1` (`g^d = z`) ⇒ `orderOf g = 2d`;
* `order_reads_sign`            — the two branches packaged as the transform;
* `sign_bit_from_order`         — the `2T = SL(2,3) → A₄` specialization at `d = 3`
                                  (order 3 `+`, order 6 `−`), matching the Python routine.

The `factorization SHAPE mod p reads ord(Frob_p)` step (Frobenius acts on the degree-24 field
as a single cycle type, so every irreducible factor has degree = the order) is the classical
Galois/finite-field realization; here we formalize the sign-from-order half exactly.

No `sorry`, no extra axioms.
-/

namespace SignOrderTransform

variable {G : Type*} [Group G]

/-- **Positive-sign branch.** If the sign is `+1` — the lift returns to the identity at the base
order, `g^d = 1`, with `d` minimal (`g^e ≠ 1` for `0 < e < d`) — then `orderOf g = d`. -/
theorem orderOf_eq_of_sign_pos (g : G) (d : ℕ) (hd : 0 < d) (hsign : g ^ d = 1)
    (hmin : ∀ e, 0 < e → e < d → g ^ e ≠ 1) : orderOf g = d := by
  have hdvd : orderOf g ∣ d := orderOf_dvd_of_pow_eq_one hsign
  have hofpos : 0 < orderOf g :=
    Nat.pos_of_ne_zero fun h => by rw [h] at hdvd; exact hd.ne' (Nat.eq_zero_of_zero_dvd hdvd)
  rcases lt_or_eq_of_le (Nat.le_of_dvd hd hdvd) with hlt | heq
  · exact absurd (pow_orderOf_eq_one g) (hmin _ hofpos hlt)
  · exact heq

/-- **Negative-sign branch.** For a central order-2 element `z` (`z² = 1`, `z ≠ 1`) and a lift
`g` whose image in `G/⟨z⟩` has order `d` (`g^e ∉ {1,z}` for `0 < e < d`), a negative sign
`g^d = z` forces the lift's order to be exactly `2d`.  (`ord = 6 = 2·3` for `Frob³ = -I` in
`SL(2,3)`.) -/
theorem orderOf_eq_two_mul_of_sign_neg (z g : G) (d : ℕ) (hd : 0 < d)
    (hz2 : z ^ 2 = 1) (hz1 : z ≠ 1) (hsign : g ^ d = z)
    (hmin : ∀ e, 0 < e → e < d → g ^ e ≠ 1 ∧ g ^ e ≠ z) : orderOf g = 2 * d := by
  have h2d : g ^ (2 * d) = 1 := by rw [mul_comm, pow_mul, hsign, hz2]
  have hpos : 0 < 2 * d := by positivity
  have hzinv : z⁻¹ = z := by rw [inv_eq_iff_mul_eq_one, ← sq, hz2]
  have hlt : ∀ k, 0 < k → k < 2 * d → g ^ k ≠ 1 := by
    intro k hk0 hk2d hk1
    rcases lt_or_ge k d with hkd | hkd
    · exact (hmin k hk0 hkd).1 hk1
    · have hkdlt : k - d < d := by omega
      have hgkd : g ^ (k - d) = z := by
        have e1 : g ^ (k - d) * g ^ d = g ^ k := by rw [← pow_add]; congr 1; omega
        rw [hsign, hk1] at e1
        rw [eq_inv_iff_mul_eq_one.mpr e1, hzinv]
      rcases Nat.eq_zero_or_pos (k - d) with h0 | hpos'
      · rw [h0, pow_zero] at hgkd; exact hz1 hgkd.symm
      · exact (hmin (k - d) hpos' hkdlt).2 hgkd
  have hdvd : orderOf g ∣ 2 * d := orderOf_dvd_of_pow_eq_one h2d
  have hofpos : 0 < orderOf g :=
    Nat.pos_of_ne_zero fun h => by rw [h] at hdvd; exact hpos.ne' (Nat.eq_zero_of_zero_dvd hdvd)
  rcases lt_or_eq_of_le (Nat.le_of_dvd hpos hdvd) with hlt2 | heq
  · exact absurd (pow_orderOf_eq_one g) (hlt _ hofpos hlt2)
  · exact heq

/-- **The sign–order transform.** With `z` central of order 2 and a lift `g` whose image in
`G/⟨z⟩` has order `d` (`g^e ∉ {1,z}` for `0<e<d`), the lift's order reads the sign:
`g^d = 1` (sign `+1`) ⇒ `orderOf g = d`; `g^d = z` (sign `−1`) ⇒ `orderOf g = 2d`. -/
theorem order_reads_sign (z g : G) (d : ℕ) (hd : 0 < d) (hz2 : z ^ 2 = 1) (hz1 : z ≠ 1)
    (hmin : ∀ e, 0 < e → e < d → g ^ e ≠ 1 ∧ g ^ e ≠ z) :
    (g ^ d = 1 → orderOf g = d) ∧ (g ^ d = z → orderOf g = 2 * d) :=
  ⟨fun h => orderOf_eq_of_sign_pos g d hd h (fun e he1 he2 => (hmin e he1 he2).1),
   fun h => orderOf_eq_two_mul_of_sign_neg z g d hd hz2 hz1 h hmin⟩

/-- **`2T = SL(2,3) → A₄`: the sign of `a_p` from `ord(Frob_p)`.**  A lift of an order-3 `A₄`
element has order 3 (sign `+1`, `Frob³=1`) or order 6 (sign `−1`, `Frob³=z`).  This is the
group-theoretic core of `rung3_lhs.sign_bit_from_order`: the degree-24 field's factorization
shape mod `p` reads `ord(Frob_p)` — 8×deg-3 ⇒ order 3 ⇒ `+`; 4×deg-6 ⇒ order 6 ⇒ `−`. -/
theorem sign_bit_from_order (z g : G) (hz2 : z ^ 2 = 1) (hz1 : z ≠ 1)
    (hmin : ∀ e, 0 < e → e < 3 → g ^ e ≠ 1 ∧ g ^ e ≠ z) :
    (g ^ 3 = 1 → orderOf g = 3) ∧ (g ^ 3 = z → orderOf g = 6) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact orderOf_eq_of_sign_pos g 3 (by norm_num) h (fun e he1 he2 => (hmin e he1 he2).1)
  · simpa using orderOf_eq_two_mul_of_sign_neg z g 3 (by norm_num) hz2 hz1 h hmin

end SignOrderTransform
