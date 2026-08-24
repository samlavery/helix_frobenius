import Mathlib

/-!
# The radial boundedness deduction

The last step of Sam's radial argument, machine-checked, together with the
multiplicative localization that unique factorization supplies.

Setting.  For a point `ρ = β + iγ` the strand magnitudes are `n^{-β}` and the
carrier radius is `∼ √n`, so the normalized strand is `A(n) ∼ n^{1/2-β}`; the
completed reflection `1 - conj ρ` gives `B(n) ∼ n^{β-1/2}`.  The pair product is
identically `1`, which carries no information; the content is *boundedness*.

Two theorems:

* `eq_one_of_pow_pair_bounded` — a positive real whose powers and inverse powers
  are jointly bounded equals `1`.  This is the localization: because the strand
  is completely multiplicative (every natural number occurs once with unit
  weight — unique factorization), the bound at a single base propagates through
  its powers, so joint boundedness at each prime already forces unit modulus.
* `eq_zero_of_rpow_pair_bounded` — if `n^δ + n^{-δ}` is bounded over `n ≥ 1`
  then `δ = 0`; with `δ = 1/2 - β` this is `β = 1/2`.

Neither theorem asserts the boundedness hypothesis.  That hypothesis is the
open input; these are the deductions that stand on top of it.
-/

namespace CriticalLinePhasor.RadialBoundedness

/-- **Localization.**  A positive real whose integer powers and their inverses are
jointly bounded is `1`.  Applied to a completely multiplicative strand this says:
joint boundedness at one base forces unit modulus at that base. -/
theorem eq_one_of_pow_pair_bounded {x C : ℝ} (hx : 0 < x)
    (h : ∀ k : ℕ, x ^ k + (x ^ k)⁻¹ ≤ C) : x = 1 := by
  rcases lt_trichotomy x 1 with hlt | heq | hgt
  · exfalso
    have hinv : 1 < x⁻¹ := one_lt_inv_iff₀.mpr ⟨hx, hlt⟩
    obtain ⟨k, hk⟩ := ((tendsto_pow_atTop_atTop_of_one_lt hinv).eventually_gt_atTop C).exists
    have hxk : 0 < x ^ k := pow_pos hx k
    have hEq : (x ^ k)⁻¹ = (x⁻¹) ^ k := by rw [inv_pow]
    have := h k
    rw [hEq] at this
    nlinarith
  · exact heq
  · exfalso
    obtain ⟨k, hk⟩ := ((tendsto_pow_atTop_atTop_of_one_lt hgt).eventually_gt_atTop C).exists
    have hxk : 0 < x ^ k := pow_pos hx k
    have hinvpos : 0 < (x ^ k)⁻¹ := inv_pos.mpr hxk
    have := h k
    linarith

/-- Powers of a completely multiplicative positive function: `f (n ^ k) = f n ^ k`. -/
theorem cm_pow {f : ℕ → ℝ} (hcm : ∀ p q : ℕ, f (p * q) = f p * f q) (hone : f 1 = 1)
    (n : ℕ) : ∀ k : ℕ, f (n ^ k) = f n ^ k := by
  intro k
  induction k with
  | zero => simpa using hone
  | succ k ih => rw [pow_succ, hcm, ih, pow_succ]

/-- **The multiplicative localization.**  For a completely multiplicative positive
function, joint boundedness of `f` and `f⁻¹` forces `f ≡ 1` on the positives.
Unique factorization is what makes checking the primes enough. -/
theorem cm_eq_one_of_bounded {f : ℕ → ℝ} {C : ℝ}
    (hpos : ∀ n : ℕ, 0 < n → 0 < f n) (hone : f 1 = 1)
    (hcm : ∀ p q : ℕ, f (p * q) = f p * f q)
    (hbdd : ∀ n : ℕ, 0 < n → f n + (f n)⁻¹ ≤ C) :
    ∀ n : ℕ, 0 < n → f n = 1 := by
  intro n hn
  refine eq_one_of_pow_pair_bounded (C := C) (hpos n hn) fun k => ?_
  have hnk : 0 < n ^ k := pow_pos hn k
  have := hbdd (n ^ k) hnk
  rwa [cm_pow hcm hone n k] at this

/-- **The radial deduction.**  If `n^δ + n^{-δ}` is bounded over `n ≥ 1` then `δ = 0`.
With `δ = 1/2 - β` this is exactly `β = 1/2`. -/
theorem eq_zero_of_rpow_pair_bounded {δ C : ℝ}
    (h : ∀ n : ℕ, 1 ≤ n → (n : ℝ) ^ δ + (n : ℝ) ^ (-δ) ≤ C) : δ = 0 := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  have hxpos : 0 < (2 : ℝ) ^ δ := Real.rpow_pos_of_pos h2 δ
  have hkey : ∀ k : ℕ, ((2 : ℝ) ^ δ) ^ k + (((2 : ℝ) ^ δ) ^ k)⁻¹ ≤ C := by
    intro k
    have hpow : ((2 : ℝ) ^ k) ^ δ = ((2 : ℝ) ^ δ) ^ k := by
      rw [← Real.rpow_natCast (2 : ℝ) k, ← Real.rpow_natCast ((2 : ℝ) ^ δ) k,
        ← Real.rpow_mul h2.le, ← Real.rpow_mul h2.le, mul_comm]
    have hpow' : ((2 : ℝ) ^ k) ^ (-δ) = (((2 : ℝ) ^ δ) ^ k)⁻¹ := by
      rw [Real.rpow_neg (by positivity), hpow]
    have hcast : (((2 ^ k : ℕ) : ℝ)) = (2 : ℝ) ^ k := by push_cast; ring
    have hn1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    have := h (2 ^ k) hn1
    rw [hcast, hpow, hpow'] at this
    exact this
  have hx1 : (2 : ℝ) ^ δ = 1 := eq_one_of_pow_pair_bounded hxpos hkey
  by_contra hδ
  rcases lt_trichotomy δ 0 with hlt | heq | hgt
  · have : (2 : ℝ) ^ δ < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hlt
    linarith
  · exact hδ heq
  · have : 1 < (2 : ℝ) ^ δ := Real.one_lt_rpow_iff_of_pos h2 |>.mpr (Or.inl ⟨by norm_num, hgt⟩)
    linarith

end CriticalLinePhasor.RadialBoundedness

section AxiomAudit
#print axioms CriticalLinePhasor.RadialBoundedness.eq_one_of_pow_pair_bounded
#print axioms CriticalLinePhasor.RadialBoundedness.cm_eq_one_of_bounded
#print axioms CriticalLinePhasor.RadialBoundedness.eq_zero_of_rpow_pair_bounded
end AxiomAudit
