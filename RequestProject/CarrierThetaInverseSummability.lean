import RequestProject.CarrierThetaDirichletInverse

/-!
# Absolute convergence of polynomial coefficient dilation couplings

Polynomial coefficient bounds on a bank and its Dirichlet inverse, together with exponential decay
of the completed carrier kernel, imply absolute summability of the double dilation series.  The
proof uses `2pq ≥ p+q` for positive integer heights to split the carrier exponential into two
polynomial-times-geometric summable tails.
-/

open Complex

namespace CriticalLinePhasor.CarrierTheta

/-- Polynomial coefficient banks coupled to an exponentially decaying carrier give an absolutely
summable product-indexed dilation series. -/
theorem polynomial_exponential_product_summable_eventually
    (u v : ℕ+ → ℂ) (h : ℝ → ℂ)
    (A B : ℕ) (Cu Cv H c x : ℝ)
    (hCu : 0 ≤ Cu) (hCv : 0 ≤ Cv) (hH : 0 ≤ H) (hc : 0 < c) (hx : 0 < x)
    (hu : ∀ n, ‖u n‖ ≤ Cu * ((n : ℕ) : ℝ) ^ A)
    (hv : ∀ n, ‖v n‖ ≤ Cv * ((n : ℕ) : ℝ) ^ B)
    (hh : ∀ᶠ p : ℕ+ × ℕ+ in Filter.cofinite,
      ‖h ((((p.1 : ℕ) * (p.2 : ℕ)) : ℝ) * x)‖ ≤
        H * Real.exp (-c * ((((p.1 : ℕ) * (p.2 : ℕ)) : ℝ) * x))) :
    Summable fun p : ℕ+ × ℕ+ =>
      u p.1 * v p.2 * h (((p.1 : ℕ) * (p.2 : ℕ)) * x) := by
  let r : ℝ := Real.exp (-(c * x) / 2)
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : ‖r‖ < 1 := by
    rw [Real.norm_of_nonneg hr0]
    dsimp [r]
    rw [Real.exp_lt_one_iff]
    nlinarith
  have hsA_nat : Summable fun n : ℕ => (n : ℝ) ^ A * r ^ n :=
    summable_pow_mul_geometric_of_norm_lt_one A hr1
  have hsB_nat : Summable fun n : ℕ => (n : ℝ) ^ B * r ^ n :=
    summable_pow_mul_geometric_of_norm_lt_one B hr1
  have hsA : Summable fun n : ℕ+ => ((n : ℕ) : ℝ) ^ A * r ^ (n : ℕ) := by
    exact hsA_nat.subtype _
  have hsB : Summable fun n : ℕ+ => ((n : ℕ) : ℝ) ^ B * r ^ (n : ℕ) := by
    exact hsB_nat.subtype _
  have hnonnegA : ∀ n : ℕ+, 0 ≤ ((n : ℕ) : ℝ) ^ A * r ^ (n : ℕ) := by
    intro n
    exact mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (pow_nonneg hr0 _)
  have hnonnegB : ∀ n : ℕ+, 0 ≤ ((n : ℕ) : ℝ) ^ B * r ^ (n : ℕ) := by
    intro n
    exact mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (pow_nonneg hr0 _)
  have hsprod : Summable fun p : ℕ+ × ℕ+ =>
      (((p.1 : ℕ) : ℝ) ^ A * r ^ (p.1 : ℕ)) *
        (((p.2 : ℕ) : ℝ) ^ B * r ^ (p.2 : ℕ)) :=
    hsA.mul_of_nonneg hsB hnonnegA hnonnegB
  have hsmajor : Summable fun p : ℕ+ × ℕ+ =>
      (Cu * Cv * H) *
        ((((p.1 : ℕ) : ℝ) ^ A * r ^ (p.1 : ℕ)) *
          (((p.2 : ℕ) : ℝ) ^ B * r ^ (p.2 : ℕ))) :=
    hsprod.mul_left (Cu * Cv * H)
  apply Summable.of_norm_bounded_eventually hsmajor
  filter_upwards [hh] with p hhp
  have hp1 : (1 : ℝ) ≤ (p.1 : ℕ) := by exact_mod_cast p.1.2
  have hp2 : (1 : ℝ) ≤ (p.2 : ℕ) := by exact_mod_cast p.2.2
  have hprodineq : ((p.1 : ℕ) : ℝ) + ((p.2 : ℕ) : ℝ) ≤
      2 * ((p.1 : ℕ) : ℝ) * ((p.2 : ℕ) : ℝ) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hp1) (sub_nonneg.mpr hp2)]
  have hexparg : -c * ((((p.1 : ℕ) * (p.2 : ℕ)) : ℝ) * x) ≤
      (-(c * x) / 2) * (p.1 : ℕ) + (-(c * x) / 2) * (p.2 : ℕ) := by
    have hneg : -(c * x) / 2 ≤ 0 := by
      have hcx : 0 < c * x := mul_pos hc hx
      linarith
    have hmul := mul_le_mul_of_nonpos_left hprodineq hneg
    nlinarith
  have hexp : Real.exp (-c * ((((p.1 : ℕ) * (p.2 : ℕ)) : ℝ) * x)) ≤
      r ^ (p.1 : ℕ) * r ^ (p.2 : ℕ) := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by simpa [r, mul_comm] using hexparg)
  calc
    ‖u p.1 * v p.2 * h ((((p.1 : ℕ) * (p.2 : ℕ)) : ℝ) * x)‖
        ≤ (Cu * ((p.1 : ℕ) : ℝ) ^ A) *
            (Cv * ((p.2 : ℕ) : ℝ) ^ B) *
              (H * Real.exp (-c * ((((p.1 : ℕ) * (p.2 : ℕ)) : ℝ) * x))) := by
          rw [norm_mul, norm_mul]
          gcongr
          · exact hu _
          · exact hv _
    _ ≤ (Cu * ((p.1 : ℕ) : ℝ) ^ A) *
            (Cv * ((p.2 : ℕ) : ℝ) ^ B) *
              (H * (r ^ (p.1 : ℕ) * r ^ (p.2 : ℕ))) := by
          gcongr
    _ = (Cu * Cv * H) *
        ((((p.1 : ℕ) : ℝ) ^ A * r ^ (p.1 : ℕ)) *
          (((p.2 : ℕ) : ℝ) ^ B * r ^ (p.2 : ℕ))) := by ring

/-- Global exponential decay is a convenient sufficient form of the cofinite dilation bound. -/
theorem polynomial_exponential_product_summable
    (u v : ℕ+ → ℂ) (h : ℝ → ℂ)
    (A B : ℕ) (Cu Cv H c x : ℝ)
    (hCu : 0 ≤ Cu) (hCv : 0 ≤ Cv) (hH : 0 ≤ H) (hc : 0 < c) (hx : 0 < x)
    (hu : ∀ n, ‖u n‖ ≤ Cu * ((n : ℕ) : ℝ) ^ A)
    (hv : ∀ n, ‖v n‖ ≤ Cv * ((n : ℕ) : ℝ) ^ B)
    (hh : ∀ t, 0 < t → ‖h t‖ ≤ H * Real.exp (-c * t)) :
    Summable fun p : ℕ+ × ℕ+ =>
      u p.1 * v p.2 * h (((p.1 : ℕ) * (p.2 : ℕ)) * x) := by
  apply polynomial_exponential_product_summable_eventually u v h A B Cu Cv H c x
    hCu hCv hH hc hx hu hv
  exact Filter.Eventually.of_forall fun p => hh _ (by positivity)

end CriticalLinePhasor.CarrierTheta

#print axioms CriticalLinePhasor.CarrierTheta.polynomial_exponential_product_summable_eventually
#print axioms CriticalLinePhasor.CarrierTheta.polynomial_exponential_product_summable
