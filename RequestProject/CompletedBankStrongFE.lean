import RequestProject.LogThetaStrongFE

/-!
# Strong functional equations for finite completed carrier banks

Every logarithmic carrier clock has polynomial growth, including the two half-shifted clocks in
the archimedean completion.  Finite products therefore have polynomial growth.  The self-dual
exponential envelope turns this into rapid decay, so the completed finite bank defines a
`StrongFEPair` with entire, vertically bounded Mellin transforms and a global functional equation.
-/

open Complex Set Filter Topology Asymptotics
open scoped BigOperators

namespace CriticalLinePhasor.StrandExchange

/-- A real translation of the logarithmic readout changes only the phases of the two exponential
terms, not their real-power norms. -/
theorem symClock_logReadout_add_real_norm_le
    (α : ℂ) (ℓ c : ℝ) {x : ℝ} (hx : 0 < x) :
    ‖CriticalLinePhasor.ChiralityHB.symClock α ℓ (logReadout x + c)‖ ≤
      x ^ (-ℓ / 2) + ‖α‖ * x ^ (ℓ / 2) := by
  unfold CriticalLinePhasor.ChiralityHB.symClock logReadout
  calc
    ‖Complex.exp (Complex.I * (Complex.I * (Real.log x : ℂ) + (c : ℂ)) * (ℓ : ℂ) / 2) -
        α * Complex.exp (-(Complex.I * (Complex.I * (Real.log x : ℂ) + (c : ℂ)) *
          (ℓ : ℂ) / 2))‖
        ≤ ‖Complex.exp (Complex.I * (Complex.I * (Real.log x : ℂ) + (c : ℂ)) *
            (ℓ : ℂ) / 2)‖ +
          ‖α * Complex.exp (-(Complex.I * (Complex.I * (Real.log x : ℂ) + (c : ℂ)) *
            (ℓ : ℂ) / 2))‖ :=
      norm_sub_le _ _
    _ = x ^ (-ℓ / 2) + ‖α‖ * x ^ (ℓ / 2) := by
      have h₁ :
          (Complex.I * (Complex.I * (Real.log x : ℂ) + (c : ℂ)) * (ℓ : ℂ) / 2).re =
            Real.log x * (-ℓ / 2) := by
        simp [Complex.mul_re, Complex.mul_im]
        ring
      have h₂ :
          (-(Complex.I * (Complex.I * (Real.log x : ℂ) + (c : ℂ)) *
            (ℓ : ℂ) / 2)).re = Real.log x * (ℓ / 2) := by
        simp [Complex.mul_re, Complex.mul_im]
        ring
      rw [norm_mul, Complex.norm_exp, Complex.norm_exp, h₁, h₂,
        Real.rpow_def_of_pos hx, Real.rpow_def_of_pos hx]

/-- Reversing the logarithmic readout swaps the two real-power exponents. -/
theorem symClock_real_sub_logReadout_norm_le
    (α : ℂ) (ℓ c : ℝ) {x : ℝ} (hx : 0 < x) :
    ‖CriticalLinePhasor.ChiralityHB.symClock α ℓ (c - logReadout x)‖ ≤
      x ^ (ℓ / 2) + ‖α‖ * x ^ (-ℓ / 2) := by
  unfold CriticalLinePhasor.ChiralityHB.symClock logReadout
  calc
    ‖Complex.exp (Complex.I * ((c : ℂ) - Complex.I * (Real.log x : ℂ)) * (ℓ : ℂ) / 2) -
        α * Complex.exp (-(Complex.I * ((c : ℂ) - Complex.I * (Real.log x : ℂ)) *
          (ℓ : ℂ) / 2))‖
        ≤ ‖Complex.exp (Complex.I * ((c : ℂ) - Complex.I * (Real.log x : ℂ)) *
            (ℓ : ℂ) / 2)‖ +
          ‖α * Complex.exp (-(Complex.I * ((c : ℂ) - Complex.I * (Real.log x : ℂ)) *
            (ℓ : ℂ) / 2))‖ :=
      norm_sub_le _ _
    _ = x ^ (ℓ / 2) + ‖α‖ * x ^ (-ℓ / 2) := by
      have h₁ :
          (Complex.I * ((c : ℂ) - Complex.I * (Real.log x : ℂ)) * (ℓ : ℂ) / 2).re =
            Real.log x * (ℓ / 2) := by
        simp [Complex.mul_re, Complex.mul_im]
        ring
      have h₂ :
          (-(Complex.I * ((c : ℂ) - Complex.I * (Real.log x : ℂ)) *
            (ℓ : ℂ) / 2)).re = Real.log x * (-ℓ / 2) := by
        simp [Complex.mul_re, Complex.mul_im]
        ring
      rw [norm_mul, Complex.norm_exp, Complex.norm_exp, h₁, h₂,
        Real.rpow_def_of_pos hx, Real.rpow_def_of_pos hx]

/-- A translated logarithmic clock is bounded by one real power. -/
theorem symClock_logReadout_add_real_isBigO
    (α : ℂ) (ℓ c : ℝ) :
    (fun x : ℝ => CriticalLinePhasor.ChiralityHB.symClock α ℓ (logReadout x + c))
      =O[atTop] (fun x : ℝ => x ^ max (-ℓ / 2) (ℓ / 2)) := by
  rw [isBigO_iff]
  refine ⟨1 + ‖α‖, ?_⟩
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hx0 : 0 < x := zero_lt_one.trans hx
  calc
    ‖CriticalLinePhasor.ChiralityHB.symClock α ℓ (logReadout x + c)‖
        ≤ x ^ (-ℓ / 2) + ‖α‖ * x ^ (ℓ / 2) :=
      symClock_logReadout_add_real_norm_le α ℓ c hx0
    _ ≤ (1 + ‖α‖) * x ^ max (-ℓ / 2) (ℓ / 2) := by
      have hneg := Real.rpow_le_rpow_of_exponent_le hx.le
        (le_max_left (-ℓ / 2) (ℓ / 2))
      have hpos := Real.rpow_le_rpow_of_exponent_le hx.le
        (le_max_right (-ℓ / 2) (ℓ / 2))
      calc
        x ^ (-ℓ / 2) + ‖α‖ * x ^ (ℓ / 2)
            ≤ x ^ max (-ℓ / 2) (ℓ / 2) + ‖α‖ * x ^ max (-ℓ / 2) (ℓ / 2) :=
          add_le_add hneg (mul_le_mul_of_nonneg_left hpos (norm_nonneg α))
        _ = (1 + ‖α‖) * x ^ max (-ℓ / 2) (ℓ / 2) := by ring
    _ = (1 + ‖α‖) * ‖x ^ max (-ℓ / 2) (ℓ / 2)‖ := by
      rw [Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _)]

/-- A reversed translated logarithmic clock is bounded by the same real power. -/
theorem symClock_real_sub_logReadout_isBigO
    (α : ℂ) (ℓ c : ℝ) :
    (fun x : ℝ => CriticalLinePhasor.ChiralityHB.symClock α ℓ (c - logReadout x))
      =O[atTop] (fun x : ℝ => x ^ max (-ℓ / 2) (ℓ / 2)) := by
  rw [isBigO_iff]
  refine ⟨1 + ‖α‖, ?_⟩
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hx0 : 0 < x := zero_lt_one.trans hx
  calc
    ‖CriticalLinePhasor.ChiralityHB.symClock α ℓ (c - logReadout x)‖
        ≤ x ^ (ℓ / 2) + ‖α‖ * x ^ (-ℓ / 2) :=
      symClock_real_sub_logReadout_norm_le α ℓ c hx0
    _ ≤ (1 + ‖α‖) * x ^ max (-ℓ / 2) (ℓ / 2) := by
      have hneg := Real.rpow_le_rpow_of_exponent_le hx.le
        (le_max_left (-ℓ / 2) (ℓ / 2))
      have hpos := Real.rpow_le_rpow_of_exponent_le hx.le
        (le_max_right (-ℓ / 2) (ℓ / 2))
      calc
        x ^ (ℓ / 2) + ‖α‖ * x ^ (-ℓ / 2)
            ≤ x ^ max (-ℓ / 2) (ℓ / 2) + ‖α‖ * x ^ max (-ℓ / 2) (ℓ / 2) :=
          add_le_add hpos (mul_le_mul_of_nonneg_left hneg (norm_nonneg α))
        _ = (1 + ‖α‖) * x ^ max (-ℓ / 2) (ℓ / 2) := by ring
    _ = (1 + ‖α‖) * ‖x ^ max (-ℓ / 2) (ℓ / 2)‖ := by
      rw [Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _)]

/-- The two half-shifted legs of the completion clock have polynomial growth. -/
theorem clockCompletion_logTheta_isBigO (α : ℂ) (ℓ : ℝ) :
    logTheta (CriticalLinePhasor.FiniteWeightFiber.clockCompletion α ℓ)
      =O[atTop] (fun x : ℝ =>
        x ^ (max (-ℓ / 2) (ℓ / 2) + max (-ℓ / 2) (ℓ / 2))) := by
  have h₁ := symClock_logReadout_add_real_isBigO α ℓ (-1 / 2)
  have h₂ := symClock_real_sub_logReadout_isBigO α ℓ (1 / 2)
  have hmul := h₁.mul h₂
  refine hmul.congr' ?_ ?_
  · filter_upwards with x
    simp only [logTheta, CriticalLinePhasor.FiniteWeightFiber.clockCompletion]
    congr 2 <;> push_cast <;> ring
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact (Real.rpow_add hx _ _).symm

/-- The logarithmic readout of any finite clock bank has polynomial growth, with exponent the sum
of the individual exponents. -/
theorem bankProduct_logTheta_isBigO {ι : Type*} (S : Finset ι)
    (α : ι → ℂ) (ℓ : ι → ℝ) :
    logTheta (bankProduct S α ℓ) =O[atTop]
      (fun x : ℝ => x ^ (∑ i ∈ S, max (-ℓ i / 2) (ℓ i / 2))) := by
  have hprod := IsBigO.finsetProd (s := S) (l := atTop)
    (fun i _ => symClock_logTheta_isBigO (α i) (ℓ i))
  refine hprod.congr' ?_ ?_
  · filter_upwards with x
    simp [logTheta, bankProduct]
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact (Real.rpow_sum_of_pos hx (fun i => max (-ℓ i / 2) (ℓ i / 2)) S).symm

/-- A finite completed-bank stage has explicit polynomial growth on the logarithmic readout. -/
theorem completedBankStage_logTheta_isBigO
    (α : ℕ → ℂ) (ℓ : ℕ → ℝ) (β : ℂ) (ℓ₀ : ℝ) (n : ℕ) :
    logTheta (completedBankStage α ℓ β ℓ₀ n) =O[atTop]
      (fun x : ℝ => x ^
        ((∑ i ∈ Finset.range n, max (-ℓ i / 2) (ℓ i / 2)) +
          (max (-ℓ₀ / 2) (ℓ₀ / 2) + max (-ℓ₀ / 2) (ℓ₀ / 2)))) := by
  have hbank := bankProduct_logTheta_isBigO (Finset.range n) α ℓ
  have hcompletion := clockCompletion_logTheta_isBigO β ℓ₀
  have hmul := hbank.mul hcompletion
  refine hmul.congr' ?_ ?_
  · filter_upwards with x
    simp [logTheta, completedBankStage, completedBank]
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact (Real.rpow_add hx _ _).symm

/-- The explicit exchange constant of a finite completed bank is unimodular. -/
theorem completedBankStageExchangeConstant_norm_one
    (α : ℕ → ℂ) (hα : ∀ i, ‖α i‖ = 1) (β : ℂ) (hβ : ‖β‖ = 1) (n : ℕ) :
    ‖completedBankStageExchangeConstant α β n‖ = 1 := by
  unfold completedBankStageExchangeConstant
  rw [norm_mul, bankProduct_star_norm_one (Finset.range n) α (fun i _ => hα i),
    norm_pow, RCLike.norm_conj, hβ]
  norm_num

/-- The explicit exchange constant of a finite completed bank is nonzero. -/
theorem completedBankStageExchangeConstant_ne_zero
    (α : ℕ → ℂ) (hα : ∀ i, ‖α i‖ = 1) (β : ℂ) (hβ : ‖β‖ = 1) (n : ℕ) :
    completedBankStageExchangeConstant α β n ≠ 0 := by
  intro hzero
  have hnorm := completedBankStageExchangeConstant_norm_one α hα β hβ n
  rw [hzero, norm_zero] at hnorm
  norm_num at hnorm

/-- The strong Riemann--Hecke pair attached to a finite completed carrier bank. -/
noncomputable def completedBankStageStrongFEPair
    (α : ℕ → ℂ) (hα : ∀ i, ‖α i‖ = 1) (ℓ : ℕ → ℝ)
    (β : ℂ) (hβ : ‖β‖ = 1) (ℓ₀ : ℝ) (n : ℕ) (k : ℝ) (hk : 0 < k) :
    StrongFEPair ℂ :=
  let A := (∑ i ∈ Finset.range n, max (-ℓ i / 2) (ℓ i / 2)) +
    (max (-ℓ₀ / 2) (ℓ₀ / 2) + max (-ℓ₀ / 2) (ℓ₀ / 2))
  strongFEPairOfLogExchange
    (completedBankStage α ℓ β ℓ₀ n)
    (completedBankStage_differentiable α ℓ β ℓ₀ n).continuous
    (completedBankStageExchangeConstant α β n)
    (completedBankStageExchangeConstant_ne_zero α hα β hβ n)
    (completedBankStage_exchange α hα ℓ β hβ ℓ₀ n)
    k hk
    (completedLogTheta_rapid_of_polynomial _ k A
      (completedBankStage_logTheta_isBigO α ℓ β ℓ₀ n))
    (completedLogThetaDual_rapid_of_polynomial _ k A
      (completedBankStage_logTheta_isBigO α ℓ β ℓ₀ n))

/-- Every finite completed carrier bank has the full twisted-niceness payload: primal and dual
Mellin transforms are entire, uniformly bounded on closed vertical strips, and satisfy the global
functional equation. -/
theorem completedBankStage_twistedNiceness
    (α : ℕ → ℂ) (hα : ∀ i, ‖α i‖ = 1) (ℓ : ℕ → ℝ)
    (β : ℂ) (hβ : ‖β‖ = 1) (ℓ₀ : ℝ) (n : ℕ) (k : ℝ) (hk : 0 < k) :
    let P := completedBankStageStrongFEPair α hα ℓ β hβ ℓ₀ n k hk
    Differentiable ℂ P.Λ ∧
    Differentiable ℂ P.symm.Λ ∧
    (∀ a b : ℝ, ∃ C : ℝ, ∀ s : ℂ,
      a ≤ s.re → s.re ≤ b → ‖P.Λ s‖ ≤ C) ∧
    (∀ a b : ℝ, ∃ C : ℝ, ∀ s : ℂ,
      a ≤ s.re → s.re ≤ b → ‖P.symm.Λ s‖ ≤ C) ∧
    (∀ s : ℂ, P.Λ (P.k - s) = P.ε • P.symm.Λ s) := by
  dsimp only
  let P := completedBankStageStrongFEPair α hα ℓ β hβ ℓ₀ n k hk
  exact ⟨P.differentiable_Λ, P.symm.differentiable_Λ,
    fun a b => CriticalLinePhasor.CarrierMellinContinuation.strongFEPair_boundedOn_verticalStrip
      P a b,
    fun a b => CriticalLinePhasor.CarrierMellinContinuation.strongFEPair_boundedOn_verticalStrip
      P.symm a b,
    P.functional_equation⟩

end CriticalLinePhasor.StrandExchange

#print axioms CriticalLinePhasor.StrandExchange.symClock_logReadout_add_real_norm_le
#print axioms CriticalLinePhasor.StrandExchange.symClock_real_sub_logReadout_norm_le
#print axioms CriticalLinePhasor.StrandExchange.clockCompletion_logTheta_isBigO
#print axioms CriticalLinePhasor.StrandExchange.bankProduct_logTheta_isBigO
#print axioms CriticalLinePhasor.StrandExchange.completedBankStage_logTheta_isBigO
#print axioms CriticalLinePhasor.StrandExchange.completedBankStageExchangeConstant_norm_one
#print axioms CriticalLinePhasor.StrandExchange.completedBankStageStrongFEPair
#print axioms CriticalLinePhasor.StrandExchange.completedBankStage_twistedNiceness
