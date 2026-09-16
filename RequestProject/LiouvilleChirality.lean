import Mathlib

/-!
# The chiral law of the carrier's winding operator

The carrier's winding operator (RH_LEDGER 719) is built from the prime dilations
`T_m : e_n ↦ e_{m·n}` weighted by von Mangoldt's `Λ`.  This file compiles the exact algebraic
law behind the measured symmetry of its spectrum (RH_LEDGER 722y, 722z):

* `gradeL` — the **Liouville grading**, multiplication by `λ(n) = (-1)^{Ω(n)}`;
* `gradeL_dilation_gradeL` — conjugating a dilation by the grading multiplies it by `λ(m)`:
  `gradeL ∘ dilation m ∘ gradeL = λ(m) • dilation m` for `m ≠ 0`;
* `gradeL_dilation_gradeL_prime` — at a prime the sign is `-1`, so **every prime atom of the
  winding operator anticommutes with the grading**, and only the even prime powers do not
  (`gradeL_dilation_gradeL_primePow`).

Consequence, recorded in the ledger and not formalised here: the spectrum of the winding
operator is symmetric about `0` up to the even-prime-power part, so it is never positive and has
no spectral gap — the seat is a statement about the fiber's own vector, never a positivity of the
operator.  This is the sieve-theoretic parity phenomenon in the carrier's coordinates.

No analysis: everything below is complete multiplicativity of `λ` (from `Ω(mn) = Ω(m) + Ω(n)`)
plus the dilation relation.
-/

open ArithmeticFunction

namespace CriticalLinePhasor.LiouvilleChirality

noncomputable section

/-- Liouville's function as a complex scalar: `λ(n) = (-1)^{Ω(n)}`. -/
def liou (n : ℕ) : ℂ := (-1) ^ (cardFactors n)

@[simp] theorem liou_one : liou 1 = 1 := by simp [liou]

/-- `λ` is completely multiplicative on nonzero arguments. -/
theorem liou_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) : liou (m * n) = liou m * liou n := by
  simp [liou, cardFactors_mul hm hn, pow_add]

/-- `λ` at a prime is `-1`. -/
theorem liou_prime {p : ℕ} (hp : p.Prime) : liou p = -1 := by
  simp [liou, cardFactors_apply_prime hp]

/-- `λ` at a prime power is `(-1)^k`. -/
theorem liou_primePow {p k : ℕ} (hp : p.Prime) : liou (p ^ k) = (-1) ^ k := by
  simp [liou, cardFactors_apply_prime_pow hp]

/-- The **dilation** `T_m : e_n ↦ e_{m·n}` on finitely supported site functions. -/
def dilation (m : ℕ) : (ℕ →₀ ℂ) →ₗ[ℂ] (ℕ →₀ ℂ) :=
  Finsupp.lmapDomain ℂ ℂ (fun n => m * n)

@[simp] theorem dilation_single (m n : ℕ) (c : ℂ) :
    dilation m (Finsupp.single n c) = Finsupp.single (m * n) c := by
  simp [dilation]

/-- The **Liouville grading** `U : e_n ↦ λ(n) e_n`. -/
def gradeL : (ℕ →₀ ℂ) →ₗ[ℂ] (ℕ →₀ ℂ) :=
  Finsupp.lsum ℂ (fun n => liou n • Finsupp.lsingle n)

@[simp] theorem gradeL_single (n : ℕ) (c : ℂ) :
    gradeL (Finsupp.single n c) = Finsupp.single n (liou n * c) := by
  classical
  simp [gradeL, Finsupp.lsum_single, Finsupp.smul_single, mul_comm]

/-- `λ(n)² = 1`, so the grading is an involution on basis vectors. -/
theorem liou_sq (n : ℕ) : liou n * liou n = 1 := by
  rw [liou, ← pow_add, ← two_mul, pow_mul]
  simp

@[simp] theorem gradeL_gradeL (f : ℕ →₀ ℂ) : gradeL (gradeL f) = f := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [map_add, hf, hg]
  | single n c => rw [gradeL_single, gradeL_single, ← mul_assoc, liou_sq, one_mul]

/-- **The chiral law**, on a carrier site `n ≠ 0`.  Conjugating the dilation `T_m` by the
Liouville grading multiplies it by `λ(m)`:
`U (T_m (U (e_n c))) = λ(m) · T_m (e_n c)` for `m ≠ 0` and `n ≠ 0`.

The hypothesis `n ≠ 0` is not cosmetic: the index `0` is a fixed point of every dilation
(`m * 0 = 0`) and is not a carrier site, and the identity genuinely fails there.  The carrier is
the span of the sites `n ≥ 1`. -/
theorem gradeL_dilation_gradeL_single {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (c : ℂ) :
    gradeL (dilation m (gradeL (Finsupp.single n c)))
      = liou m • dilation m (Finsupp.single n c) := by
  classical
  simp only [gradeL_single, dilation_single, Finsupp.smul_single, smul_eq_mul]
  rw [liou_mul hm hn]
  congr 1
  calc liou m * liou n * (liou n * c)
      = liou m * (liou n * liou n) * c := by ring
    _ = liou m * c := by rw [liou_sq]; ring

/-- **Every prime atom anticommutes with the grading**: at a prime the conjugated dilation is
`-T_p` on every carrier site.  This is the source of the winding operator's symmetric spectrum. -/
theorem gradeL_dilation_gradeL_prime {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0) (c : ℂ) :
    gradeL (dilation p (gradeL (Finsupp.single n c)))
      = -(dilation p (Finsupp.single n c)) := by
  rw [gradeL_dilation_gradeL_single hp.ne_zero hn, liou_prime hp]
  simp

/-- **The defect is exactly the even prime powers**: `U T_{p^k} U = (-1)^k T_{p^k}`, so the atoms
that do NOT flip sign are precisely those with `k` even.  Against the primes' weight this is the
squares, and it is the whole obstruction to an exactly symmetric spectrum. -/
theorem gradeL_dilation_gradeL_primePow {p k n : ℕ} (hp : p.Prime) (hn : n ≠ 0) (c : ℂ) :
    gradeL (dilation (p ^ k) (gradeL (Finsupp.single n c)))
      = ((-1 : ℂ) ^ k) • dilation (p ^ k) (Finsupp.single n c) := by
  rw [gradeL_dilation_gradeL_single (pow_ne_zero k hp.ne_zero) hn, liou_primePow hp]

end

end CriticalLinePhasor.LiouvilleChirality

#print axioms CriticalLinePhasor.LiouvilleChirality.liou_mul
#print axioms CriticalLinePhasor.LiouvilleChirality.gradeL_dilation_gradeL_single
#print axioms CriticalLinePhasor.LiouvilleChirality.gradeL_gradeL
#print axioms CriticalLinePhasor.LiouvilleChirality.gradeL_dilation_gradeL_prime
#print axioms CriticalLinePhasor.LiouvilleChirality.gradeL_dilation_gradeL_primePow
