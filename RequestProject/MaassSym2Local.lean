import RequestProject.MaassMuPeel

/-!
# The Maass Sym² bank at prime powers

`maassSym2Bank (p^j) = h_j(α_p², 1, α_p⁻²)` — the local factors of the Sym² bank are the
Sym²-Satake traces.  This is the arithmetic content of the wire, and the last piece before the
edge argument.

The two inputs are `maass_muRankin_prime_pow` (the Möbius peel) and
`Sym2CoefficientIdentification.sym2Coeff_eq_sum_peeled`, and the latter is stated **generically in
the Satake parameter** — it never mentions a modular form.  So the only Maass-specific content is
the peel, which came from the eigenvalue recursion and reality.

**Provenance.**  Ported by substitution from `sym2Bank_prime_pow`; the divisor bookkeeping is
unchanged.

**Scope.**  `r = 2`.  Sato--Tate needs every rank; this is not a route to it.
-/

open ArithmeticFunction Complex Finset
open scoped Real ArithmeticFunction.Moebius

namespace CriticalLinePhasor.Unfolding

open CriticalLinePhasor.GeneralSeed CriticalLinePhasor.ThreeDConverse
open CriticalLinePhasor.Sym2Identification CriticalLinePhasor.Sym2Wire

theorem maass_sym2Bank_prime_pow (M : GenuineMaassCuspForm3D) (p : Nat.Primes) (j : ℕ) :
    maassSym2Bank M (p.1 ^ j) = Sym2Identification.sym2Coeff (M.eigenData.satake p) j := by
  unfold maassSym2Bank
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal
      (f := fun d e => sqIndicator d *
        ((μ : ArithmeticFunction ℂ) * maassRankinSquareNorm M) e),
    Nat.divisors_prime_pow p.2, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk]
  have hdiv : ∀ i ∈ Finset.range (j + 1), (p.1 : ℕ) ^ j / p ^ i = p ^ (j - i) := by
    intro i hi
    have hij : i ≤ j := by
      have := Finset.mem_range.mp hi
      omega
    rw [Nat.pow_div hij p.2.pos]
  rw [Finset.sum_congr rfl fun i hi => by
    rw [hdiv i hi, sqIndicator_prime_pow p.2 i, maass_muRankin_prime_pow M p (j - i)]]
  -- extract the even indices and reindex by halves
  rw [Finset.sum_congr rfl fun i _ => (ite_mul _ _ _ _).trans (by rw [one_mul, zero_mul]),
    ← Finset.sum_filter]
  rw [sym2Coeff_eq_sum_peeled (M.eigenData.satake p) (M.eigenData.satake_ne_zero p) j]
  refine Finset.sum_nbij' (fun i => i / 2) (fun m => 2 * m) ?_ ?_ ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    simp only [Finset.mem_range]
    omega
  · intro m hm
    simp only [Finset.mem_range] at hm
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · omega
    · exact ⟨m, by omega⟩
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    obtain ⟨-, m, hm⟩ := hi
    omega
  · intro m _
    omega
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    obtain ⟨-, m, hm⟩ := hi
    congr 1
    omega

end CriticalLinePhasor.Unfolding

#print axioms CriticalLinePhasor.Unfolding.maass_sym2Bank_prime_pow
