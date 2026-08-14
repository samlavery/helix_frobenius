import RequestProject.GeneralSeed

/-!
# Growth of the Maass Hecke eigenvalues at prime powers

`MaassEigenData` constrains its eigenvalues at *primes* (`lam_bound`).  The Fourier--Whittaker
summability argument needs a bound at every index; this file supplies the prime-power half, the
arithmetic step that the analysis in `MaassCoeffSummable` deliberately left as a hypothesis.

**Which bound is inductive.**  The naive target `‖lam (p^k)‖ ≤ (k+1)·p^(k·E₀)` is *not* provable
from the Hecke recursion by triangle inequality: `lam (p^(j+2)) = lam p · lam (p^(j+1)) - lam (p^j)`
gives `(j+2)·p^((j+2)E₀) + (j+1)·p^(jE₀)`, and absorbing the second term into the first would need
`j+1 ≤ p^(2E₀)`, which fails for large `j` (and always when `E₀ = 0`).  The recursion is
Fibonacci-shaped, so the honest bound carries the base `p^E₀ + 1`:

  `‖lam (p^k)‖ ≤ (k+1) · (p^E₀ + 1)^k`.

With `C = B + 1` the induction closes with room to spare — `C²(j+3) - BC(j+2) = (B+1)(B+j+3)`,
which dominates the leftover `j+1`.  Since `p^E₀ + 1 ≤ 2·p^E₀ ≤ p^(E₀+1)` for `p ≥ 2` and
`E₀ ≥ 0`, this is still polynomial in the index, which is all the summability argument needs.

The multiplicativity step propagating to all `n` is not taken here.
-/

namespace CriticalLinePhasor.GeneralSeed

/-- **Prime-power growth of the Hecke eigenvalues.**  The Hecke recursion is Fibonacci-shaped, so
the inductive bound carries the base `p^E₀ + 1`. -/
theorem lam_prime_pow_bound (M : MaassEigenData) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    ‖M.lam (p ^ k)‖ ≤ ((k : ℝ) + 1) * ((p : ℝ) ^ M.E₀ + 1) ^ k := by
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.one_le
  have hB : (0 : ℝ) ≤ (p : ℝ) ^ M.E₀ := by positivity
  set B : ℝ := (p : ℝ) ^ M.E₀ with hBdef
  have hC1 : (1 : ℝ) ≤ B + 1 := by linarith
  have hCpos : (0 : ℝ) < B + 1 := by linarith
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 => simp [M.one]
    | 1 =>
        have hb := M.lam_bound p hp
        rw [pow_one]
        have hCk : (B + 1) ^ 1 = B + 1 := pow_one _
        rw [hCk]
        push_cast
        calc ‖M.lam p‖ ≤ B := hb
          _ ≤ (1 + 1) * (B + 1) := by nlinarith
    | (j + 2) =>
        have hrec := M.prime_rec p hp j
        have ih1 : ‖M.lam (p ^ (j + 1))‖ ≤ ((j : ℝ) + 2) * (B + 1) ^ (j + 1) := by
          have := ih (j + 1) (by omega)
          push_cast at this ⊢
          linarith
        have ih0 : ‖M.lam (p ^ j)‖ ≤ ((j : ℝ) + 1) * (B + 1) ^ j := by
          have := ih j (by omega)
          push_cast at this ⊢
          linarith
        have hb := M.lam_bound p hp
        have hCj : (0 : ℝ) < (B + 1) ^ j := by positivity
        rw [hrec]
        refine le_trans (norm_sub_le _ _) ?_
        rw [norm_mul]
        have hstep1 : ‖M.lam p‖ * ‖M.lam (p ^ (j + 1))‖ ≤
            B * (((j : ℝ) + 2) * (B + 1) ^ (j + 1)) := by
          apply mul_le_mul hb ih1 (norm_nonneg _) hB
        have hpow1 : (B + 1) ^ (j + 1) = (B + 1) ^ j * (B + 1) := pow_succ _ _
        have hpow2 : (B + 1) ^ (j + 2) = (B + 1) ^ j * ((B + 1) * (B + 1)) := by
          rw [pow_succ, pow_succ]
          ring
        push_cast
        calc ‖M.lam p‖ * ‖M.lam (p ^ (j + 1))‖ + ‖M.lam (p ^ j)‖
            ≤ B * (((j : ℝ) + 2) * (B + 1) ^ (j + 1)) + ((j : ℝ) + 1) * (B + 1) ^ j :=
              add_le_add hstep1 ih0
          _ = (B + 1) ^ j * (B * (B + 1) * ((j : ℝ) + 2) + ((j : ℝ) + 1)) := by
              rw [hpow1]; ring
          _ ≤ (B + 1) ^ j * (((B + 1) * (B + 1)) * ((j : ℝ) + 3)) := by
              apply mul_le_mul_of_nonneg_left _ (le_of_lt hCj)
              nlinarith [hB, Nat.cast_nonneg (α := ℝ) j]
          _ = ((j : ℝ) + 2 + 1) * (B + 1) ^ (j + 2) := by
              rw [hpow2]; ring

/-- The prime-power bound in clean polynomial form.  Both combinatorial factors are absorbed by
powers of `p`: `k+1 ≤ 2^k ≤ p^k` and `p^E₀ + 1 ≤ 2·p^E₀ ≤ p^(E₀+1)`. -/
theorem lam_prime_pow_le_pow (M : MaassEigenData) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    ‖M.lam (p ^ k)‖ ≤ ((p : ℝ) ^ k) ^ (M.E₀ + 2) := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by linarith
  have hppos : (0 : ℝ) < (p : ℝ) := by linarith
  have hB : (1 : ℝ) ≤ (p : ℝ) ^ M.E₀ := one_le_pow₀ hp1
  -- `k + 1 ≤ p ^ k`
  have hcount : ((k : ℝ) + 1) ≤ (p : ℝ) ^ k := by
    have h2 : ((k : ℝ) + 1) ≤ (2 : ℝ) ^ k := by
      have hnat : k + 1 ≤ 2 ^ k := Nat.lt_two_pow_self
      have hcast : ((k + 1 : ℕ) : ℝ) ≤ ((2 ^ k : ℕ) : ℝ) := by exact_mod_cast hnat
      push_cast at hcast
      linarith
    exact le_trans h2 (pow_le_pow_left₀ (by norm_num) hp2 k)
  -- `(p^E₀ + 1)^k ≤ (p^(E₀+1))^k`
  have hbase : ((p : ℝ) ^ M.E₀ + 1) ≤ (p : ℝ) ^ (M.E₀ + 1) := by
    rw [pow_succ]
    nlinarith [hB, hp2]
  have hbasek : ((p : ℝ) ^ M.E₀ + 1) ^ k ≤ ((p : ℝ) ^ (M.E₀ + 1)) ^ k :=
    pow_le_pow_left₀ (by positivity) hbase k
  refine le_trans (lam_prime_pow_bound M hp k) ?_
  have hstep : ((k : ℝ) + 1) * ((p : ℝ) ^ M.E₀ + 1) ^ k ≤
      (p : ℝ) ^ k * ((p : ℝ) ^ (M.E₀ + 1)) ^ k := by
    apply mul_le_mul hcount hbasek (by positivity) (by positivity)
  refine le_trans hstep (le_of_eq ?_)
  rw [← pow_mul, ← pow_mul, ← pow_add]
  congr 1
  ring

/-- **Polynomial growth of the Hecke eigenvalues at every index.**  Multiplicativity on coprime
arguments propagates the prime-power bound, and the exponents add exactly. -/
theorem lam_norm_le (M : MaassEigenData) (n : ℕ) (hn : n ≠ 0) :
    ‖M.lam n‖ ≤ (n : ℝ) ^ (M.E₀ + 2) := by
  revert hn
  induction n using Nat.recOnPrimeCoprime with
  | zero => intro h; exact absurd rfl h
  | prime_pow p k hp =>
      intro _
      have h := lam_prime_pow_le_pow M hp k
      rwa [← Nat.cast_pow] at h
  | coprime a b ha hb hab iha ihb =>
      intro _
      have ha0 : a ≠ 0 := by omega
      have hb0 : b ≠ 0 := by omega
      rw [M.coprime_mul a b hab, norm_mul]
      have hA := iha ha0
      have hB := ihb hb0
      calc ‖M.lam a‖ * ‖M.lam b‖ ≤ (a : ℝ) ^ (M.E₀ + 2) * (b : ℝ) ^ (M.E₀ + 2) :=
            mul_le_mul hA hB (norm_nonneg _) (by positivity)
        _ = ((a : ℝ) * (b : ℝ)) ^ (M.E₀ + 2) := (mul_pow _ _ _).symm
        _ = ((a * b : ℕ) : ℝ) ^ (M.E₀ + 2) := by push_cast; ring

end CriticalLinePhasor.GeneralSeed

#print axioms CriticalLinePhasor.GeneralSeed.lam_prime_pow_bound
#print axioms CriticalLinePhasor.GeneralSeed.lam_prime_pow_le_pow
#print axioms CriticalLinePhasor.GeneralSeed.lam_norm_le
