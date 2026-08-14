import RequestProject.CPSLocalEulerLogDerivative3D
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

/-!
# Prime-power support of generalized Rankin--Selberg von Mangoldt coefficients

This file proves the missing global support theorem.  For any multiplicative arithmetic
coefficient function, its logarithmically weighted Dirichlet convolution with its canonical
inverse is supported on prime powers.  The retained conventional Rankin--Selberg logarithmic
coefficient is then an immediate specialization.
-/

open Finset Nat

namespace ArithmeticFunction

/-- The multiplicative arithmetic function prescribed by arbitrary values on prime powers. -/
noncomputable def primePowerMultiplicativeExtension3D
    (v : ℕ → ℕ → ℂ) : ArithmeticFunction ℂ where
  toFun n := if n = 0 then 0 else n.factorization.prod v
  map_zero' := by simp

/-- The factorization extension is multiplicative because coprime integers have disjoint prime
support. -/
theorem primePowerMultiplicativeExtension3D_isMultiplicative
    (v : ℕ → ℕ → ℂ) :
    (primePowerMultiplicativeExtension3D v).IsMultiplicative := by
  rw [IsMultiplicative.iff_ne_zero]
  constructor
  · change (if (1 : ℕ) = 0 then 0 else (1 : ℕ).factorization.prod v) = 1
    simp
  · intro m n hm hn hmn
    change (if m * n = 0 then 0 else (m * n).factorization.prod v) =
      (if m = 0 then 0 else m.factorization.prod v) *
        (if n = 0 then 0 else n.factorization.prod v)
    rw [if_neg (mul_ne_zero hm hn), if_neg hm, if_neg hn, Nat.factorization_mul hm hn]
    apply Finsupp.prod_add_index_of_disjoint
    simpa only [support_factorization] using hmn.disjoint_primeFactors

/-- Evaluation of the multiplicative extension on a prime power. -/
theorem primePowerMultiplicativeExtension3D_prime_pow
    (v : ℕ → ℕ → ℂ) {p k : ℕ} (hp : p.Prime) :
    primePowerMultiplicativeExtension3D v (p ^ k) =
      if k = 0 then 1 else v p k := by
  cases k with
  | zero =>
      change (if p ^ 0 = 0 then 0 else (p ^ 0).factorization.prod v) = 1
      simp
  | succ k =>
      change (if p ^ (k + 1) = 0 then 0 else (p ^ (k + 1)).factorization.prod v) =
        v p (k + 1)
      rw [if_neg (pow_ne_zero _ hp.ne_zero), factorization_pow, hp.factorization]
      have hs : (k + 1) • (Finsupp.single p 1 : ℕ →₀ ℕ) =
          Finsupp.single p (k + 1) := by
        ext q
        simp [mul_comm]
      change (((k + 1) • (Finsupp.single p 1 : ℕ →₀ ℕ)).prod v) =
        v p (k + 1)
      rw [hs]
      rw [Finsupp.prod, Finsupp.support_single p (by omega)]
      simp

/-- The canonical Dirichlet inverse of a multiplicative complex arithmetic function is
multiplicative. -/
theorem dirichletInverse_isMultiplicative3D
    (A : ArithmeticFunction ℂ) (hA : A.IsMultiplicative)
    (h1 : Invertible (A 1)) :
    (dirichletInverse A h1).IsMultiplicative := by
  let I := dirichletInverse A h1
  let J := primePowerMultiplicativeExtension3D (fun p k ↦ I (p ^ k))
  have hJ : J.IsMultiplicative :=
    primePowerMultiplicativeExtension3D_isMultiplicative _
  have hAJ : A * J = 1 := by
    apply (IsMultiplicative.eq_iff_eq_on_prime_powers
      (A * J) (hA.mul hJ) 1 isMultiplicative_one).2
    intro p k hp
    rw [CriticalLinePhasor.TransportClosure.mul_apply_prime_pow A J hp k]
    have hAI := congrFun (congrArg DFunLike.coe
      (self_mul_dirichletInverse A h1)) (p ^ k)
    rw [CriticalLinePhasor.TransportClosure.mul_apply_prime_pow A I hp k] at hAI
    calc
      ∑ a ∈ range (k + 1), A (p ^ a) * J (p ^ (k - a)) =
          ∑ a ∈ range (k + 1), A (p ^ a) * I (p ^ (k - a)) := by
        apply Finset.sum_congr rfl
        intro a _
        congr 1
        unfold J
        rw [primePowerMultiplicativeExtension3D_prime_pow _ hp]
        split_ifs with hz
        · simp [hz, I, hA]
        · rfl
      _ = (1 : ArithmeticFunction ℂ) (p ^ k) := hAI
  have hJI : J = I := by
    calc
      J = 1 * J := by rw [one_mul]
      _ = (I * A) * J := by rw [dirichletInverse_mul_self]
      _ = I * (A * J) := by ring
      _ = I := by rw [hAJ, mul_one]
  change I.IsMultiplicative
  rw [← hJI]
  exact hJ

/-- Multiplication of coefficients by the complex logarithm of their index. -/
noncomputable def complexLogWeight3D (A : ArithmeticFunction ℂ) : ArithmeticFunction ℂ where
  toFun n := Complex.log (n : ℂ) * A n
  map_zero' := by simp

/-- Restriction of an arithmetic function to prime powers. -/
noncomputable def primePowerRestriction3D (g : ArithmeticFunction ℂ) : ArithmeticFunction ℂ where
  toFun n := if IsPrimePow n then g n else 0
  map_zero' := by simp [not_isPrimePow_zero]

/-- The complex logarithm of a positive natural product is additive. -/
theorem complex_log_nat_mul3D {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    Complex.log ((a * b : ℕ) : ℂ) =
      Complex.log (a : ℂ) + Complex.log (b : ℂ) := by
  rw [← Complex.natCast_log, ← Complex.natCast_log, ← Complex.natCast_log,
    Nat.cast_mul, Real.log_mul (Nat.cast_ne_zero.mpr ha) (Nat.cast_ne_zero.mpr hb)]
  norm_cast

/-- Prime-power restriction does not change any prime-power value when the value at one is zero. -/
theorem primePowerRestriction3D_eq_self_prime_pow
    (g : ArithmeticFunction ℂ) (hg1 : g 1 = 0) {p k : ℕ} (hp : p.Prime) :
    primePowerRestriction3D g (p ^ k) = g (p ^ k) := by
  cases k with
  | zero => simp [primePowerRestriction3D, hg1]
  | succ k =>
      simp [primePowerRestriction3D, hp.isPrimePow.pow (Nat.succ_ne_zero k)]

/-- At a coprime product, convolution of a prime-power-supported function with a multiplicative
function splits into its two prime supports. -/
theorem primePowerRestriction3D_mul_of_coprime
    (A g : ArithmeticFunction ℂ) (hA : A.IsMultiplicative)
    {a b : ℕ} (hab : a.Coprime b) :
    (primePowerRestriction3D g * A) (a * b) =
      (primePowerRestriction3D g * A) a * A b +
        A a * (primePowerRestriction3D g * A) b := by
  simp only [ArithmeticFunction.mul_apply]
  rw [Nat.sum_divisorsAntidiagonal fun d e ↦ primePowerRestriction3D g d * A e]
  rw [Nat.sum_divisorsAntidiagonal fun d e ↦ primePowerRestriction3D g d * A e]
  rw [Nat.sum_divisorsAntidiagonal fun d e ↦ primePowerRestriction3D g d * A e]
  change (∑ d ∈ (a * b).divisors,
      (if IsPrimePow d then g d else 0) * A (a * b / d)) =
    (∑ d ∈ a.divisors, (if IsPrimePow d then g d else 0) * A (a / d)) * A b +
      A a * (∑ d ∈ b.divisors,
        (if IsPrimePow d then g d else 0) * A (b / d))
  simp only [ite_mul, zero_mul, ← Finset.sum_filter]
  change (∑ d ∈ (a * b).divisors.filter IsPrimePow,
      g d * A (a * b / d)) =
    (∑ d ∈ a.divisors.filter IsPrimePow, g d * A (a / d)) * A b +
      A a * (∑ d ∈ b.divisors.filter IsPrimePow, g d * A (b / d))
  rw [Nat.mul_divisors_filter_prime_pow hab, Finset.filter_union,
    Finset.sum_union (Nat.disjoint_divisors_filter_isPrimePow hab)]
  congr 1
  · calc
      ∑ d ∈ {d ∈ a.divisors | IsPrimePow d},
          g d * A (a * b / d) =
          ∑ d ∈ {d ∈ a.divisors | IsPrimePow d},
            (g d * A (a / d)) * A b := by
        apply Finset.sum_congr rfl
        intro d hd
        rw [Finset.mem_filter, Nat.mem_divisors] at hd
        rw [mul_comm a b, Nat.mul_div_assoc b hd.1.1, mul_comm b (a / d),
          hA.map_mul_of_coprime]
        · ring
        · exact hab.coprime_dvd_left (Nat.div_dvd_of_dvd hd.1.1)
      _ = (∑ d ∈ {d ∈ a.divisors | IsPrimePow d},
            g d * A (a / d)) * A b := by rw [Finset.sum_mul]
  · calc
      ∑ d ∈ {d ∈ b.divisors | IsPrimePow d},
          g d * A (a * b / d) =
          ∑ d ∈ {d ∈ b.divisors | IsPrimePow d},
            A a * (g d * A (b / d)) := by
        apply Finset.sum_congr rfl
        intro d hd
        rw [Finset.mem_filter, Nat.mem_divisors] at hd
        rw [Nat.mul_div_assoc a hd.1.1, hA.map_mul_of_coprime]
        · ring
        · exact hab.coprime_dvd_right (Nat.div_dvd_of_dvd hd.1.1)
      _ = A a * (∑ d ∈ {d ∈ b.divisors | IsPrimePow d},
            g d * A (b / d)) := by rw [Finset.mul_sum]

/-- The generalized von Mangoldt convolution is exactly its prime-power restriction. -/
theorem generalizedVonMangoldt_eq_primePowerRestriction3D
    (A : ArithmeticFunction ℂ) (hA : A.IsMultiplicative)
    (h1 : Invertible (A 1)) :
    primePowerRestriction3D
        (complexLogWeight3D A * dirichletInverse A h1) =
      complexLogWeight3D A * dirichletInverse A h1 := by
  let I := dirichletInverse A h1
  let g := complexLogWeight3D A * I
  let H := primePowerRestriction3D g
  have hg1 : g 1 = 0 := by
    rw [show g = complexLogWeight3D A * I from rfl, ArithmeticFunction.mul_apply_one]
    simp [complexLogWeight3D]
  have hgA : g * A = complexLogWeight3D A := by
    calc
      g * A = complexLogWeight3D A * (I * A) := by simp [g]; ring
      _ = complexLogWeight3D A * 1 := by
        change complexLogWeight3D A * (dirichletInverse A h1 * A) =
          complexLogWeight3D A * 1
        rw [dirichletInverse_mul_self]
      _ = complexLogWeight3D A := by rw [mul_one]
  have hHA : H * A = complexLogWeight3D A := by
    ext n
    refine Nat.recOnPrimeCoprime ?_ ?_ ?_ n
    · simp [H, primePowerRestriction3D, complexLogWeight3D]
    · intro p k hp
      rw [CriticalLinePhasor.TransportClosure.mul_apply_prime_pow H A hp k,
        ← congrFun (congrArg DFunLike.coe hgA) (p ^ k),
        CriticalLinePhasor.TransportClosure.mul_apply_prime_pow g A hp k]
      apply Finset.sum_congr rfl
      intro a _
      congr 1
      exact primePowerRestriction3D_eq_self_prime_pow g hg1 hp
    · intro a b ha hb hab ha_ind hb_ind
      rw [primePowerRestriction3D_mul_of_coprime A g hA hab]
      rw [ha_ind, hb_ind]
      change (Complex.log (a : ℂ) * A a) * A b +
          A a * (Complex.log (b : ℂ) * A b) =
        Complex.log ((a * b : ℕ) : ℂ) * A (a * b)
      rw [hA.map_mul_of_coprime hab, complex_log_nat_mul3D (by omega) (by omega)]
      ring
  change H = g
  calc
    H = H * 1 := by rw [mul_one]
    _ = H * (A * I) := by
      change H * 1 = H * (A * dirichletInverse A h1)
      rw [self_mul_dirichletInverse]
    _ = (H * A) * I := by ring
    _ = complexLogWeight3D A * I := by rw [hHA]
    _ = g := rfl

/-- A generalized von Mangoldt coefficient vanishes away from prime powers. -/
theorem generalizedVonMangoldt_eq_zero_of_not_isPrimePow3D
    (A : ArithmeticFunction ℂ) (hA : A.IsMultiplicative)
    (h1 : Invertible (A 1)) {n : ℕ} (hn : ¬ IsPrimePow n) :
    (complexLogWeight3D A * dirichletInverse A h1) n = 0 := by
  rw [← generalizedVonMangoldt_eq_primePowerRestriction3D A hA h1]
  simp [primePowerRestriction3D, hn]

end ArithmeticFunction

namespace CriticalLinePhasor.GlobalHelix
namespace ConventionalCompletedRankinSelbergSource3D

variable {r m : ℕ} {pi : PolynomialSatakeDualPair (Fin 2)}
  {tau : PolynomialSatakeDualPair (Fin m)}
  {D : ArithmeticCPSCompletionData r m}

/-- The logarithmic coefficient of every conventional completed Rankin--Selberg source is
globally supported on prime powers. -/
theorem logarithmicCoefficient_eq_zero_of_not_isPrimePow
    (L : ConventionalCompletedRankinSelbergSource3D r m pi tau D)
    {n : ℕ} (hn : ¬ IsPrimePow n) :
    L.logarithmicCoefficient n = 0 := by
  change (ArithmeticFunction.complexLogWeight3D L.arithmeticCoefficient *
    ArithmeticFunction.dirichletInverse L.arithmeticCoefficient
      L.arithmeticCoefficientOneInvertible) n = 0
  exact ArithmeticFunction.generalizedVonMangoldt_eq_zero_of_not_isPrimePow3D
    L.arithmeticCoefficient
    (CriticalLinePhasor.TransportClosure.isMultiplicative_bankArithmetic _)
    L.arithmeticCoefficientOneInvertible hn

end ConventionalCompletedRankinSelbergSource3D
end CriticalLinePhasor.GlobalHelix

#print axioms ArithmeticFunction.dirichletInverse_isMultiplicative3D
#print axioms ArithmeticFunction.generalizedVonMangoldt_eq_zero_of_not_isPrimePow3D
#print axioms CriticalLinePhasor.GlobalHelix.ConventionalCompletedRankinSelbergSource3D.logarithmicCoefficient_eq_zero_of_not_isPrimePow
