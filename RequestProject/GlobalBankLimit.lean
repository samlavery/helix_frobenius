import RequestProject.StrandExchange

/-!
# Global limits of completed carrier banks

This file closes the analytic passage from finite completed banks to a global limit.  Local-uniform
convergence preserves entire-ness, and the finite-stage strand exchange survives when its explicit
exchange constants converge.  It then specializes both statements to the finite-range stages of
`StrandExchange.completedBank`.
-/

open Complex Set Filter Topology CriticalLinePhasor.ChiralityHB
open scoped BigOperators

namespace CriticalLinePhasor.StrandExchange

/-- A locally uniform limit of entire finite carrier stages is entire. -/
theorem locallyUniformLimit_differentiable
    {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hconv : TendstoLocallyUniformly F f atTop)
    (hdiff : ∀ n, Differentiable ℂ (F n)) :
    Differentiable ℂ f := by
  rw [← tendstoLocallyUniformlyOn_univ] at hconv
  rw [← differentiableOn_univ]
  exact hconv.differentiableOn
    (Filter.Eventually.of_forall fun n => (hdiff n).differentiableOn) isOpen_univ

/-- An exact finite-stage exchange law passes to a locally uniform limit.  The exchange constants
may vary with the stage, provided that they converge. -/
theorem locallyUniformLimit_exchange
    {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} {εs : ℕ → ℂ} {ε : ℂ}
    (hconv : TendstoLocallyUniformly F f atTop)
    (hε : Tendsto εs atTop (𝓝 ε))
    (hexchange : ∀ n z,
      (starRingEnd ℂ) (F n ((starRingEnd ℂ) z)) = εs n * F n z) :
    ∀ z, (starRingEnd ℂ) (f ((starRingEnd ℂ) z)) = ε * f z := by
  intro z
  have hconvOn : TendstoLocallyUniformlyOn F f atTop Set.univ :=
    tendstoLocallyUniformlyOn_univ.mpr hconv
  have hleft : Tendsto
      (fun n => (starRingEnd ℂ) (F n ((starRingEnd ℂ) z))) atTop
      (𝓝 ((starRingEnd ℂ) (f ((starRingEnd ℂ) z)))) :=
    Complex.continuous_conj.continuousAt.tendsto.comp
      (hconvOn.tendsto_at (Set.mem_univ ((starRingEnd ℂ) z)))
  have hright : Tendsto (fun n => εs n * F n z) atTop (𝓝 (ε * f z)) :=
    hε.mul (hconvOn.tendsto_at (Set.mem_univ z))
  have hfun :
      (fun n => (starRingEnd ℂ) (F n ((starRingEnd ℂ) z))) =
        (fun n => εs n * F n z) := by
    funext n
    exact hexchange n z
  rw [hfun] at hleft
  exact tendsto_nhds_unique hleft hright

/-- The `n`th completed carrier stage: truncate the clock bank to `Finset.range n`. -/
noncomputable def completedBankStage
    (α : ℕ → ℂ) (ℓ : ℕ → ℝ) (β : ℂ) (ℓ₀ : ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  completedBank (Finset.range n) α ℓ β ℓ₀ z

/-- The explicit exchange constant of `completedBankStage`. -/
noncomputable def completedBankStageExchangeConstant
    (α : ℕ → ℂ) (β : ℂ) (n : ℕ) : ℂ :=
  (∏ i ∈ Finset.range n, (-(starRingEnd ℂ) (α i))) * ((starRingEnd ℂ) β) ^ 2

/-- Every finite-range completed carrier stage obeys the exact exchange law. -/
theorem completedBankStage_exchange
    (α : ℕ → ℂ) (hα : ∀ i, ‖α i‖ = 1) (ℓ : ℕ → ℝ)
    (β : ℂ) (hβ : ‖β‖ = 1) (ℓ₀ : ℝ) (n : ℕ) (z : ℂ) :
    (starRingEnd ℂ) (completedBankStage α ℓ β ℓ₀ n ((starRingEnd ℂ) z)) =
      completedBankStageExchangeConstant α β n * completedBankStage α ℓ β ℓ₀ n z := by
  simpa [completedBankStage, completedBankStageExchangeConstant] using
    completedBank_star (Finset.range n) α (fun i _ => hα i) ℓ β hβ ℓ₀ z

/-- Every finite-range completed carrier stage is entire. -/
theorem completedBankStage_differentiable
    (α : ℕ → ℂ) (ℓ : ℕ → ℝ) (β : ℂ) (ℓ₀ : ℝ) (n : ℕ) :
    Differentiable ℂ (completedBankStage α ℓ β ℓ₀ n) := by
  unfold completedBankStage completedBank bankProduct
  apply Differentiable.mul
  · have h_each : ∀ i ∈ Finset.range n,
        Differentiable ℂ (fun z => symClock (α i) (ℓ i) z) := by
      intro i _
      unfold symClock
      fun_prop
    have h := Differentiable.finsetProd (u := Finset.range n)
      (f := fun i => fun z => symClock (α i) (ℓ i) z) h_each
    convert h using 1 <;> try rfl
    funext z
    rw [Finset.prod_fn]
  · exact CriticalLinePhasor.FiniteWeightFiber.clockCompletion_differentiable β ℓ₀

/-- The global completed-bank assembly: a locally uniform carrier limit is entire and inherits the
global exchange law from the explicit finite stages. -/
theorem completedBankLimit_entire_exchange
    (α : ℕ → ℂ) (hα : ∀ i, ‖α i‖ = 1) (ℓ : ℕ → ℝ)
    (β : ℂ) (hβ : ‖β‖ = 1) (ℓ₀ : ℝ) (f : ℂ → ℂ) (ε : ℂ)
    (hconv : TendstoLocallyUniformly (completedBankStage α ℓ β ℓ₀) f atTop)
    (hε : Tendsto (completedBankStageExchangeConstant α β) atTop (𝓝 ε)) :
    Differentiable ℂ f ∧
      ∀ z, (starRingEnd ℂ) (f ((starRingEnd ℂ) z)) = ε * f z := by
  exact ⟨locallyUniformLimit_differentiable hconv
      (completedBankStage_differentiable α ℓ β ℓ₀),
    locallyUniformLimit_exchange hconv hε
      (completedBankStage_exchange α hα ℓ β hβ ℓ₀)⟩

end CriticalLinePhasor.StrandExchange

#print axioms CriticalLinePhasor.StrandExchange.locallyUniformLimit_differentiable
#print axioms CriticalLinePhasor.StrandExchange.locallyUniformLimit_exchange
#print axioms CriticalLinePhasor.StrandExchange.completedBankStage_exchange
#print axioms CriticalLinePhasor.StrandExchange.completedBankStage_differentiable
#print axioms CriticalLinePhasor.StrandExchange.completedBankLimit_entire_exchange
