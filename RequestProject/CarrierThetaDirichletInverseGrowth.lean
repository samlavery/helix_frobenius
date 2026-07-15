import RequestProject.CarrierThetaAsymptoticCoupling
import Mathlib.NumberTheory.ZetaValues

/-!
# Polynomial growth of Dirichlet inverses

A polynomially bounded arithmetic function with invertible first coefficient has a polynomially
bounded Dirichlet inverse.  The proof uses the defining proper-divisor recursion and a uniform
power-sum bound obtained from the convergent reciprocal-square series.
-/

open Complex BigOperators

namespace CriticalLinePhasor.CarrierTheta

open ArithmeticFunction

/-- The squares of the proper divisors have a uniform quadratic majorant. -/
theorem properDivisors_sq_le_three_mul_sq (n : ℕ) :
    ∑ d ∈ n.properDivisors, ((d : ℝ) ^ 2) ≤ 3 * (n : ℝ) ^ 2 := by
  let q : {d // d ∈ n.properDivisors} → ℕ := fun d => n / (d : ℕ)
  have hqinj : Function.Injective q := by
    intro d e hqde
    have hd := (Nat.mem_properDivisors.mp d.2).1
    have he := (Nat.mem_properDivisors.mp e.2).1
    have hdprod : (d : ℕ) * (n / (d : ℕ)) = n := Nat.mul_div_cancel' hd
    have heprod : (e : ℕ) * (n / (e : ℕ)) = n := Nat.mul_div_cancel' he
    change n / (d : ℕ) = n / (e : ℕ) at hqde
    apply Subtype.ext
    apply Nat.mul_right_cancel
      (Nat.zero_lt_of_lt (Nat.one_lt_div_of_mem_properDivisors d.2))
    calc
      (d : ℕ) * (n / (d : ℕ)) = n := hdprod
      _ = (e : ℕ) * (n / (e : ℕ)) := heprod.symm
      _ = (e : ℕ) * (n / (d : ℕ)) := by rw [hqde]
  have hsummable : Summable (fun m : ℕ => 1 / (m : ℝ) ^ 2) := hasSum_zeta_two.summable
  have hquot := tsum_comp_le_tsum_of_inj hsummable (fun m => by positivity) hqinj
  rw [tsum_fintype, hasSum_zeta_two.tsum_eq] at hquot
  have hzeta : Real.pi ^ 2 / 6 ≤ 3 := by
    nlinarith [Real.pi_pos, Real.pi_lt_four]
  have hquot3 : (∑ d : {d // d ∈ n.properDivisors},
      1 / ((q d : ℕ) : ℝ) ^ 2) ≤ 3 := le_trans hquot hzeta
  rw [← Finset.sum_attach]
  calc
    ∑ d : {d // d ∈ n.properDivisors}, ((d : ℕ) : ℝ) ^ 2 =
        (n : ℝ) ^ 2 * ∑ d : {d // d ∈ n.properDivisors},
          (1 / ((q d : ℕ) : ℝ) ^ 2) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro d _
            have hdprod : (d : ℕ) * (n / (d : ℕ)) = n :=
              Nat.mul_div_cancel' (Nat.mem_properDivisors.mp d.2).1
            have hqpos : 0 < q d :=
              Nat.zero_lt_of_lt (Nat.one_lt_div_of_mem_properDivisors d.2)
            have hdprodR : ((d : ℕ) : ℝ) * ((q d : ℕ) : ℝ) = (n : ℝ) := by
              exact_mod_cast hdprod
            rw [← hdprodR]
            field_simp
    _ ≤ (n : ℝ) ^ 2 * 3 := mul_le_mul_of_nonneg_left hquot3 (sq_nonneg _)
    _ = 3 * (n : ℝ) ^ 2 := by ring

/-- Raising the divisor weights increases the contraction by a power of two. -/
theorem properDivisors_power_sum_bound (n E : ℕ) :
    (2 : ℝ) ^ E * (∑ d ∈ n.properDivisors, (d : ℝ) ^ (E + 2)) ≤
      3 * (n : ℝ) ^ (E + 2) := by
  calc
    (2 : ℝ) ^ E * (∑ d ∈ n.properDivisors, (d : ℝ) ^ (E + 2)) =
        ∑ d ∈ n.properDivisors, (2 : ℝ) ^ E * (d : ℝ) ^ (E + 2) := by
          simp [Finset.mul_sum]
    _ ≤ ∑ d ∈ n.properDivisors, (n : ℝ) ^ E * (d : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro d hd
      have hdvd := (Nat.mem_properDivisors.mp hd).1
      have hq := Nat.one_lt_div_of_mem_properDivisors hd
      have htwoNat : 2 * d ≤ n := by
        calc
          2 * d ≤ (n / d) * d := Nat.mul_le_mul_right d hq
          _ = n := by rw [Nat.div_mul_cancel hdvd]
      have htwo : (2 : ℝ) * d ≤ n := by exact_mod_cast htwoNat
      have hpow : ((2 : ℝ) * d) ^ E ≤ (n : ℝ) ^ E := by
        gcongr
      calc
        (2 : ℝ) ^ E * (d : ℝ) ^ (E + 2) =
            (((2 : ℝ) * d) ^ E) * (d : ℝ) ^ 2 := by ring
        _ ≤ (n : ℝ) ^ E * (d : ℝ) ^ 2 := by gcongr
    _ = (n : ℝ) ^ E * (∑ d ∈ n.properDivisors, (d : ℝ) ^ 2) := by
      rw [Finset.mul_sum]
    _ ≤ (n : ℝ) ^ E * (3 * (n : ℝ) ^ 2) := by
      gcongr
      exact properDivisors_sq_le_three_mul_sq n
    _ = 3 * (n : ℝ) ^ (E + 2) := by ring

/-- Quantitative strong-induction bound for the recursive inverse. -/
theorem dirichletInverseFun_polynomial_bound_of_scale
    (a : ℕ → ℂ) (ha : Invertible (a 1))
    (A E : ℕ) (Ca : ℝ) (hCa : 0 ≤ Ca)
    (haBound : ∀ n : ℕ, ‖a n‖ ≤ Ca * (n : ℝ) ^ A)
    (hscale : 3 * ‖⅟(a 1)‖ * Ca ≤ (2 : ℝ) ^ E) :
    ∀ n : ℕ, ‖dirichletInverseFun a ha n‖ ≤
      ‖⅟(a 1)‖ * (n : ℝ) ^ (A + E + 2) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn0 : n = 0
      · subst n
        simp
      by_cases hn1 : n = 1
      · subst n
        simp
      rw [ArithmeticFunction.dirichletInverseFun_apply_ne a ha hn0 hn1]
      have hsumNorm :
          ‖∑ d ∈ n.properDivisors, a (n / d) * dirichletInverseFun a ha d‖ ≤
            ∑ d ∈ n.properDivisors,
              (Ca * ((n / d : ℕ) : ℝ) ^ A) *
                (‖⅟(a 1)‖ * (d : ℝ) ^ (A + E + 2)) := by
        calc
          ‖∑ d ∈ n.properDivisors, a (n / d) * dirichletInverseFun a ha d‖ ≤
              ∑ d ∈ n.properDivisors,
                ‖a (n / d) * dirichletInverseFun a ha d‖ :=
                  norm_sum_le n.properDivisors _
          _ ≤ ∑ d ∈ n.properDivisors,
              (Ca * ((n / d : ℕ) : ℝ) ^ A) *
                (‖⅟(a 1)‖ * (d : ℝ) ^ (A + E + 2)) := by
            apply Finset.sum_le_sum
            intro d hd
            rw [norm_mul]
            apply mul_le_mul (haBound _) (ih d (Nat.mem_properDivisors.mp hd).2)
            · exact norm_nonneg _
            · positivity
      have hsumFactor :
          (∑ d ∈ n.properDivisors,
              (Ca * ((n / d : ℕ) : ℝ) ^ A) *
                (‖⅟(a 1)‖ * (d : ℝ) ^ (A + E + 2))) =
            Ca * ‖⅟(a 1)‖ * (n : ℝ) ^ A *
              (∑ d ∈ n.properDivisors, (d : ℝ) ^ (E + 2)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d hd
        have hdvd := (Nat.mem_properDivisors.mp hd).1
        have hprod : (n / d) * d = n := Nat.div_mul_cancel hdvd
        have hprodR : ((n / d : ℕ) : ℝ) * (d : ℝ) = (n : ℝ) := by
          exact_mod_cast hprod
        rw [← hprodR]
        ring
      have hsumNonneg : 0 ≤ ∑ d ∈ n.properDivisors, (d : ℝ) ^ (E + 2) := by
        positivity
      have hscaleSum := mul_le_mul_of_nonneg_right hscale hsumNonneg
      have hdiv := properDivisors_power_sum_bound n E
      have hcontract :
          ‖⅟(a 1)‖ * Ca *
              (∑ d ∈ n.properDivisors, (d : ℝ) ^ (E + 2)) ≤
            (n : ℝ) ^ (E + 2) := by
        have hthree :
            3 * (‖⅟(a 1)‖ * Ca *
              (∑ d ∈ n.properDivisors, (d : ℝ) ^ (E + 2))) ≤
              3 * (n : ℝ) ^ (E + 2) := by
          calc
            3 * (‖⅟(a 1)‖ * Ca *
                (∑ d ∈ n.properDivisors, (d : ℝ) ^ (E + 2))) =
                (3 * ‖⅟(a 1)‖ * Ca) *
                  (∑ d ∈ n.properDivisors, (d : ℝ) ^ (E + 2)) := by ring
            _ ≤ (2 : ℝ) ^ E *
                  (∑ d ∈ n.properDivisors, (d : ℝ) ^ (E + 2)) := hscaleSum
            _ ≤ 3 * (n : ℝ) ^ (E + 2) := hdiv
        linarith
      calc
        ‖-⅟(a 1) * ∑ d ∈ n.properDivisors,
            a (n / d) * dirichletInverseFun a ha d‖ =
            ‖⅟(a 1)‖ *
              ‖∑ d ∈ n.properDivisors,
                a (n / d) * dirichletInverseFun a ha d‖ := by simp
        _ ≤ ‖⅟(a 1)‖ *
            (∑ d ∈ n.properDivisors,
              (Ca * ((n / d : ℕ) : ℝ) ^ A) *
                (‖⅟(a 1)‖ * (d : ℝ) ^ (A + E + 2))) := by
              gcongr
        _ = ‖⅟(a 1)‖ * (n : ℝ) ^ A *
            (‖⅟(a 1)‖ * Ca *
              (∑ d ∈ n.properDivisors, (d : ℝ) ^ (E + 2))) := by
              rw [hsumFactor]
              ring
        _ ≤ ‖⅟(a 1)‖ * (n : ℝ) ^ A * (n : ℝ) ^ (E + 2) := by
              gcongr
        _ = ‖⅟(a 1)‖ * (n : ℝ) ^ (A + E + 2) := by ring

/-- A polynomial coefficient bound supplies a polynomial bound for the Dirichlet inverse. -/
theorem dirichletInverse_polynomial_bound
    (a : ArithmeticFunction ℂ) (ha : Invertible (a 1))
    (A : ℕ) (Ca : ℝ) (hCa : 0 ≤ Ca)
    (haBound : ∀ n : ℕ, ‖a n‖ ≤ Ca * (n : ℝ) ^ A) :
    ∃ B : ℕ, ∃ Cb : ℝ, 0 ≤ Cb ∧
      ∀ n : ℕ+, ‖(dirichletInverse a ha) n‖ ≤ Cb * ((n : ℕ) : ℝ) ^ B := by
  obtain ⟨E, hE⟩ := pow_unbounded_of_one_lt
    (3 * ‖⅟(a 1)‖ * Ca) (by norm_num : (1 : ℝ) < 2)
  refine ⟨A + E + 2, ‖⅟(a 1)‖, norm_nonneg _, ?_⟩
  intro n
  exact dirichletInverseFun_polynomial_bound_of_scale
    a ha A E Ca hCa haBound hE.le (n : ℕ)

end CriticalLinePhasor.CarrierTheta

#print axioms CriticalLinePhasor.CarrierTheta.properDivisors_sq_le_three_mul_sq
#print axioms CriticalLinePhasor.CarrierTheta.properDivisors_power_sum_bound
#print axioms CriticalLinePhasor.CarrierTheta.dirichletInverseFun_polynomial_bound_of_scale
#print axioms CriticalLinePhasor.CarrierTheta.dirichletInverse_polynomial_bound
