import RequestProject.SameHeightPartner

/-!
# Sites versus continuum: the two halves of the HP conversion (ledger 1227)

**On the sites** (sequences indexed by `n ≥ 1`):
* `partner_pairing_eq_harmonic`: the bank of a zero and the bank of its same-height partner pair to exactly the
  drift-free mass, `Σ_{n≤N} n^{−ρ}·conj(n^{−ρ*}) = Σ_{n≤N} n^{−1}`, for EVERY `ρ`. It does not depend on `δ` or `γ`.
* `intDil_bank`: the native dilations act on sites only as the integer-dilation maps `(M_k f)(n) = f(kn)`, with the
  bank as joint eigenvector, `M_k B(s) = k^{−s}·B(s)`.
* `intDil_kills_first_site`: `M_k` (k ≥ 2) annihilates the first site. On sites the dilations form a
  non-injective semigroup, not a unitary group, so they give no reality constraint.

**On the continuum** (area measure, `AreaDilation`): the dilations are unitary and the generator is symmetric, but
zero-states are not normalizable (`DilationEigen`, `SymmetricPairing`).

So the native construction has the two halves separately: sites carry normalizable states and a positive,
`δ`-independent partner pairing, but no symmetry; the continuum carries the symmetry but no normalizable
zero-states. The HP conversion is a single space with BOTH. Not constructed here.
-/

open Complex Finset

noncomputable section

namespace CriticalLinePhasor.SitesContinuum

open CriticalLinePhasor.SameHeight

/-- **The partner pairing of banks is the drift-free mass, independent of `ρ`.** -/
theorem partner_pairing_eq_harmonic (N : ℕ) (ρ : ℂ) :
    ∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-ρ) * (starRingEnd ℂ) ((n : ℂ) ^ (-(partner ρ))) =
      ∑ n ∈ Finset.Icc 1 N, ((n : ℝ)⁻¹ : ℂ) := by
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hpow : (n : ℂ) ^ (-ρ) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]; tauto
  rw [bank_partner_inversion hn1, map_div₀, Complex.conj_conj]
  have hconj1 : (starRingEnd ℂ) ((n : ℂ) ^ (-1 : ℂ)) = (n : ℂ)⁻¹ := by
    rw [Complex.cpow_neg_one, map_inv₀, Complex.conj_natCast]
  rw [hconj1]
  push_cast
  field_simp

/-- The integer dilation on sequences. -/
def intDil (k : ℕ) (f : ℕ → ℂ) (n : ℕ) : ℂ := f (k * n)

/-- **The bank is a joint eigenvector of the integer dilations.** -/
theorem intDil_bank {k : ℕ} (hk : 1 ≤ k) (s : ℂ) (n : ℕ) :
    intDil k (fun m => (m : ℂ) ^ (-s)) n = (k : ℂ) ^ (-s) * (n : ℂ) ^ (-s) := by
  unfold intDil
  push_cast
  rw [show ((k : ℂ) * n) = (((k : ℝ) * n : ℝ) : ℂ) by push_cast; ring,
    Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity)]
  push_cast
  ring

/-- **On sites the dilations are not injective**: `M_k` (k ≥ 2) annihilates the first site. -/
theorem intDil_kills_first_site {k : ℕ} (hk : 2 ≤ k) :
    intDil k (fun m => if m = 1 then (1 : ℂ) else 0) = 0 := by
  funext n
  unfold intDil
  have h : k * n ≠ 1 := fun h => by
    have := Nat.eq_one_of_mul_eq_one_right h
    omega
  simp [h]

end CriticalLinePhasor.SitesContinuum

end

#print axioms CriticalLinePhasor.SitesContinuum.partner_pairing_eq_harmonic
#print axioms CriticalLinePhasor.SitesContinuum.intDil_bank
#print axioms CriticalLinePhasor.SitesContinuum.intDil_kills_first_site
