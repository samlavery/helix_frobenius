import RequestProject.CarrierThetaExponentialDecay
import RequestProject.CarrierThetaInverseSummability

/-!
# Asymptotic carrier tails discharge Dirichlet-inverse coupling convergence

Positive integer dilation products escape every bounded interval except for finitely many index
pairs.  Thus an exponential `atTop` bound on the completed carrier supplies the cofinite comparison
needed for absolute summability of the Dirichlet-inverse coupling.  Polynomial bounds on the
coefficient bank and its inverse then give an exact coefficient-theta realization of the completed
carrier.
-/

open Complex Set Filter Topology Asymptotics

namespace CriticalLinePhasor.CarrierTheta

open ArithmeticFunction CriticalLinePhasor.StrandExchange

/-- Positive dilation products tend to infinity along the cofinite filter on pairs. -/
theorem tendsto_pnat_mul_const_cofinite_atTop {x : ℝ} (hx : 0 < x) :
    Tendsto (fun p : ℕ+ × ℕ+ => (((p.1 : ℕ) * (p.2 : ℕ)) : ℝ) * x)
      cofinite atTop := by
  rw [tendsto_atTop]
  intro b
  obtain ⟨N : ℕ, hN⟩ := exists_nat_gt (b / x)
  rw [eventually_cofinite]
  apply Set.Finite.subset
    (show Set.Finite {p : ℕ+ × ℕ+ | (p.1 : ℕ) ≤ N ∧ (p.2 : ℕ) ≤ N} by
      have h1 : Set.Finite {p : ℕ+ | (p : ℕ) ≤ N} := by
        exact Set.Finite.preimage Subtype.val_injective.injOn (Set.finite_Iic N)
      exact h1.prod h1)
  intro p hp
  simp only [Set.mem_setOf_eq, not_le] at hp ⊢
  have hp1 : ((p.1 : ℕ) : ℝ) ≤ (((p.1 : ℕ) * (p.2 : ℕ)) : ℝ) := by
    exact_mod_cast Nat.le_mul_of_pos_right (p.1 : ℕ) p.2.2
  have hp2 : ((p.2 : ℕ) : ℝ) ≤ (((p.1 : ℕ) * (p.2 : ℕ)) : ℝ) := by
    exact_mod_cast Nat.le_mul_of_pos_left (p.2 : ℕ) p.1.2
  have hprodlt : (((p.1 : ℕ) * (p.2 : ℕ)) : ℝ) < b / x := by
    rw [lt_div_iff₀ hx]
    exact hp
  constructor
  · have hlt : ((p.1 : ℕ) : ℝ) < N := lt_of_le_of_lt hp1 (lt_trans hprodlt hN)
    have hltNat : (p.1 : ℕ) < N := by exact_mod_cast hlt
    exact hltNat.le
  · have hlt : ((p.2 : ℕ) : ℝ) < N := lt_of_le_of_lt hp2 (lt_trans hprodlt hN)
    have hltNat : (p.2 : ℕ) < N := by exact_mod_cast hlt
    exact hltNat.le

/-- An exponential carrier tail and polynomial coefficient bounds imply absolute convergence of
the product-indexed dilation coupling. -/
theorem polynomial_product_summable_of_exp_tail
    (u v : ℕ+ → ℂ) (h : ℝ → ℂ)
    (A B : ℕ) (Cu Cv : ℝ) {x : ℝ} (hx : 0 < x)
    (hCu : 0 ≤ Cu) (hCv : 0 ≤ Cv)
    (hu : ∀ n, ‖u n‖ ≤ Cu * ((n : ℕ) : ℝ) ^ A)
    (hv : ∀ n, ‖v n‖ ≤ Cv * ((n : ℕ) : ℝ) ^ B)
    (hh : h =O[atTop] (fun t : ℝ => Real.exp (-t / 2))) :
    Summable fun p : ℕ+ × ℕ+ =>
      u p.1 * v p.2 * h (((p.1 : ℕ) * (p.2 : ℕ)) * x) := by
  rw [isBigO_iff'] at hh
  obtain ⟨H, hH, hh⟩ := hh
  have hhc := (tendsto_pnat_mul_const_cofinite_atTop hx).eventually hh
  apply polynomial_exponential_product_summable_eventually
    u v h A B Cu Cv H (1 / 2) x hCu hCv hH.le (by norm_num) hx hu hv
  filter_upwards [hhc] with p hp
  rw [Real.norm_of_nonneg (Real.exp_nonneg _)] at hp
  convert hp using 1 <;> ring

/-- The completed primal carrier has an absolutely summable inverse-kernel coupling whenever the
coefficient bank and its Dirichlet inverse have polynomial bounds. -/
theorem completedLogTheta_inverseSeries_summable
    (a : ArithmeticFunction ℂ) (ha : Invertible (a 1))
    (E : ℂ → ℂ) (k Acar : ℝ)
    (hpoly : logTheta E =O[atTop] (fun x : ℝ => x ^ Acar))
    (A B : ℕ) (Ca Cb : ℝ) {x : ℝ} (hx : 0 < x)
    (hCa : 0 ≤ Ca) (hCb : 0 ≤ Cb)
    (haBound : ∀ n : ℕ+, ‖a n‖ ≤ Ca * ((n : ℕ) : ℝ) ^ A)
    (hbBound : ∀ n : ℕ+, ‖(dirichletInverse a ha) n‖ ≤ Cb * ((n : ℕ) : ℝ) ^ B) :
    Summable fun p : ℕ+ × ℕ+ =>
      a p.1 * (dirichletInverse a ha) p.2 *
        completedLogTheta E k (((p.1 : ℕ) * (p.2 : ℕ)) * x) :=
  polynomial_product_summable_of_exp_tail (fun n => a n) (fun n => (dirichletInverse a ha) n)
    (completedLogTheta E k) A B Ca Cb hx hCa hCb haBound hbBound
    (completedLogTheta_isBigO_exp_neg_half E k Acar hpoly)

/-- The completed dual carrier has the same absolutely summable inverse-kernel coupling. -/
theorem completedLogThetaDual_inverseSeries_summable
    (a : ArithmeticFunction ℂ) (ha : Invertible (a 1))
    (E : ℂ → ℂ) (k Acar : ℝ)
    (hpoly : logTheta E =O[atTop] (fun x : ℝ => x ^ Acar))
    (A B : ℕ) (Ca Cb : ℝ) {x : ℝ} (hx : 0 < x)
    (hCa : 0 ≤ Ca) (hCb : 0 ≤ Cb)
    (haBound : ∀ n : ℕ+, ‖a n‖ ≤ Ca * ((n : ℕ) : ℝ) ^ A)
    (hbBound : ∀ n : ℕ+, ‖(dirichletInverse a ha) n‖ ≤ Cb * ((n : ℕ) : ℝ) ^ B) :
    Summable fun p : ℕ+ × ℕ+ =>
      a p.1 * (dirichletInverse a ha) p.2 *
        completedLogThetaDual E k (((p.1 : ℕ) * (p.2 : ℕ)) * x) :=
  polynomial_product_summable_of_exp_tail (fun n => a n) (fun n => (dirichletInverse a ha) n)
    (completedLogThetaDual E k) A B Ca Cb hx hCa hCb haBound hbBound
    (completedLogThetaDual_isBigO_exp_neg_half E k Acar hpoly)

/-- Exact primal carrier-to-coefficient-theta coupling with the convergence obligation discharged
by polynomial coefficient bounds and the completed carrier's exponential tail. -/
theorem theta_dirichletInverse_completedLogTheta
    (a : ℕ → ℂ) (ha : Invertible ((coefficientArithmetic a) 1))
    (E : ℂ → ℂ) (k Acar : ℝ)
    (hpoly : logTheta E =O[atTop] (fun x : ℝ => x ^ Acar))
    (A B : ℕ) (Ca Cb : ℝ) {x : ℝ} (hx : 0 < x)
    (hCa : 0 ≤ Ca) (hCb : 0 ≤ Cb)
    (haBound : ∀ n : ℕ+, ‖(coefficientArithmetic a) n‖ ≤
      Ca * ((n : ℕ) : ℝ) ^ A)
    (hbBound : ∀ n : ℕ+, ‖(dirichletInverse (coefficientArithmetic a) ha) n‖ ≤
      Cb * ((n : ℕ) : ℝ) ^ B) :
    theta a
      (dilationKernel (dirichletInverse (coefficientArithmetic a) ha)
        (completedLogTheta E k)) x = completedLogTheta E k x := by
  apply theta_dirichletInverse_coupling
  exact completedLogTheta_inverseSeries_summable (coefficientArithmetic a) ha E k Acar hpoly
    A B Ca Cb hx hCa hCb haBound hbBound

end CriticalLinePhasor.CarrierTheta

#print axioms CriticalLinePhasor.CarrierTheta.tendsto_pnat_mul_const_cofinite_atTop
#print axioms CriticalLinePhasor.CarrierTheta.polynomial_product_summable_of_exp_tail
#print axioms CriticalLinePhasor.CarrierTheta.completedLogTheta_inverseSeries_summable
#print axioms CriticalLinePhasor.CarrierTheta.completedLogThetaDual_inverseSeries_summable
#print axioms CriticalLinePhasor.CarrierTheta.theta_dirichletInverse_completedLogTheta
