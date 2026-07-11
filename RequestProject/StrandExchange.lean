import RequestProject.CompletedReflectionFiber

/-!
# The global strand exchange of the finite bank

The paper's `prop:completedFE` step (2) — the carrier reflection — is assembled place
by place from the per-clock weld law `ChiralityHB.symClock_star`:

    E*_{α,ℓ}(z̄) = −ᾱ · E_{α,ℓ}(z)      (`symClock_star`, unit clock face `‖α‖ = 1`).

This file performs the **global strand exchange**: the same conjugation law for the finite
product bank

    E(z) = ∏_{i ∈ S} E_{α_i, ℓ_i}(z),

over a finite index set `S`.  The bank's star-conjugate is the bank itself times the explicit
unimodular constant `ε = ∏_{i ∈ S} (−ᾱ_i)`:

    E*(z̄) = ε · E(z),      `‖ε‖ = 1`.

* `bankProduct_star` — the exchange identity, from the per-place law by `Finset.prod`
  induction (`map_prod` for the conjugation, `Finset.prod_mul_distrib` to split off `ε`);
* `bankProduct_star_norm_one` — the exchange constant `ε` is unimodular;
* `bankProduct_exchange` — 1 + 2 packaged as `∃ ε, ‖ε‖ = 1 ∧ E*(z̄) = ε·E(z)`, the paper's
  `E*(z̄) = ε·E(z)` with `ε` explicit;
* `completedBank_star` / `completedBank_exchange` — the same conjugation exchange for the
  completed finite bank `E(z)·γ(z)`, where `γ = FiniteWeightFiber.clockCompletion β ℓ₀`
  is the archimedean clock-completion object of `CompletedReflectionFiber`.  Its exchange
  constant is `ε · β̄²`, still unimodular.

**Scope.**  This is the **finite-stage** bank (finite `S`) and its **conjugation** strand
exchange `z ↦ z̄`.  The infinite-bank limit is not claimed here.  The `s ↦ 1-s` completed
functional equation is a *different* reflection — the self-duality
`FiniteWeightFiber.clockCompletion_selfdual` / `symTensorCompleted_FE`; it is not what this
file proves.  No `axiom`, no `sorry`; nothing here assumes or proves RH/GRH.
-/

open Complex CriticalLinePhasor.ChiralityHB
open scoped BigOperators

namespace CriticalLinePhasor.StrandExchange

/-- The finite product bank `E(z) = ∏_{i ∈ S} symClock (α i) (ℓ i) z`. -/
noncomputable def bankProduct {ι : Type*} (S : Finset ι) (α : ι → ℂ) (ℓ : ι → ℝ) (z : ℂ) : ℂ :=
  ∏ i ∈ S, symClock (α i) (ℓ i) z

/-- **The global strand exchange (identity form).**  The star-conjugate of the finite bank at
`z̄` equals the explicit constant `ε = ∏_{i ∈ S} (−ᾱ_i)` times the bank at `z`.  Assembled from
the per-place weld law `symClock_star` by `Finset.prod` induction: `map_prod` distributes the
conjugation over the product, and `Finset.prod_mul_distrib` splits off `ε`.  Finite `S`; unit
clock faces. -/
theorem bankProduct_star {ι : Type*} (S : Finset ι) (α : ι → ℂ)
    (hα : ∀ i ∈ S, ‖α i‖ = 1) (ℓ : ι → ℝ) (z : ℂ) :
    (starRingEnd ℂ) (∏ i ∈ S, symClock (α i) (ℓ i) ((starRingEnd ℂ) z))
      = (∏ i ∈ S, (-(starRingEnd ℂ) (α i))) * (∏ i ∈ S, symClock (α i) (ℓ i) z) := by
  rw [map_prod, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i hi => symClock_star (hα i hi) (ℓ i) z

/-- **The exchange constant is unimodular.**  `ε = ∏_{i ∈ S} (−ᾱ_i)` has `‖ε‖ = 1` when every
clock face is unit (`‖α i‖ = 1`): each factor has norm `‖−ᾱ_i‖ = ‖α_i‖ = 1`. -/
theorem bankProduct_star_norm_one {ι : Type*} (S : Finset ι) (α : ι → ℂ)
    (hα : ∀ i ∈ S, ‖α i‖ = 1) :
    ‖∏ i ∈ S, (-(starRingEnd ℂ) (α i))‖ = 1 := by
  rw [norm_prod]
  apply Finset.prod_eq_one
  intro i hi
  rw [norm_neg, RCLike.norm_conj, hα i hi]

/-- **The global strand exchange (packaged form).**  There is a unimodular constant `ε` with
`E*(z̄) = ε·E(z)` for all `z`, where `E = bankProduct S α ℓ` — the paper's `E*(z̄) = ε·E(z)` for
the finite bank, with `ε = ∏_{i ∈ S} (−ᾱ_i)` explicit.  Finite `S`; unit clock faces.  The
infinite-bank limit is not claimed. -/
theorem bankProduct_exchange {ι : Type*} (S : Finset ι) (α : ι → ℂ)
    (hα : ∀ i ∈ S, ‖α i‖ = 1) (ℓ : ι → ℝ) :
    ∃ ε : ℂ, ‖ε‖ = 1 ∧ ∀ z : ℂ,
      (starRingEnd ℂ) (bankProduct S α ℓ ((starRingEnd ℂ) z)) = ε * bankProduct S α ℓ z := by
  refine ⟨∏ i ∈ S, (-(starRingEnd ℂ) (α i)), bankProduct_star_norm_one S α hα, fun z => ?_⟩
  exact bankProduct_star S α hα ℓ z

/-- **The completion clock's strand exchange.**  The archimedean clock-completion factor
`γ(z) = FiniteWeightFiber.clockCompletion α ℓ z = symClock α ℓ (z−½)·symClock α ℓ (½−z)` obeys
the conjugation exchange `γ*(z̄) = ᾱ²·γ(z)` (each of its two `symClock` legs contributes a
`−ᾱ`, and `(−ᾱ)² = ᾱ²`).  Unit clock face `‖α‖ = 1`. -/
theorem clockCompletion_star {α : ℂ} (hα : ‖α‖ = 1) (ℓ : ℝ) (z : ℂ) :
    (starRingEnd ℂ) (CriticalLinePhasor.FiniteWeightFiber.clockCompletion α ℓ ((starRingEnd ℂ) z))
      = ((starRingEnd ℂ) α) ^ 2 * CriticalLinePhasor.FiniteWeightFiber.clockCompletion α ℓ z := by
  have hhalf : (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 := by
    rw [map_div₀, map_one, map_ofNat]
  have h1 : (starRingEnd ℂ) z - 1 / 2 = (starRingEnd ℂ) (z - 1 / 2) := by
    rw [map_sub, hhalf]
  have h2 : (1 : ℂ) / 2 - (starRingEnd ℂ) z = (starRingEnd ℂ) (1 / 2 - z) := by
    rw [map_sub, hhalf]
  unfold CriticalLinePhasor.FiniteWeightFiber.clockCompletion
  rw [map_mul, h1, h2, symClock_star hα, symClock_star hα]
  ring

/-- The completed finite bank `E(z)·γ(z)`: the bank product times the archimedean
clock-completion factor `γ = FiniteWeightFiber.clockCompletion β ℓ₀` of
`CompletedReflectionFiber`. -/
noncomputable def completedBank {ι : Type*} (S : Finset ι) (α : ι → ℂ) (ℓ : ι → ℝ)
    (β : ℂ) (ℓ₀ : ℝ) (z : ℂ) : ℂ :=
  bankProduct S α ℓ z * CriticalLinePhasor.FiniteWeightFiber.clockCompletion β ℓ₀ z

/-- **The completed strand exchange (identity form).**  The star-conjugate of the completed
finite bank at `z̄` equals the explicit constant `(∏_{i ∈ S} (−ᾱ_i))·β̄²` times the completed
bank at `z`.  The bank contributes `∏ (−ᾱ_i)` (`bankProduct_star`) and the completion clock
contributes `β̄²` (`clockCompletion_star`).  Finite `S`; unit clock faces `‖α i‖ = 1`, `‖β‖ = 1`. -/
theorem completedBank_star {ι : Type*} (S : Finset ι) (α : ι → ℂ)
    (hα : ∀ i ∈ S, ‖α i‖ = 1) (ℓ : ι → ℝ) (β : ℂ) (hβ : ‖β‖ = 1) (ℓ₀ : ℝ) (z : ℂ) :
    (starRingEnd ℂ) (completedBank S α ℓ β ℓ₀ ((starRingEnd ℂ) z))
      = ((∏ i ∈ S, (-(starRingEnd ℂ) (α i))) * ((starRingEnd ℂ) β) ^ 2)
        * completedBank S α ℓ β ℓ₀ z := by
  unfold completedBank bankProduct
  rw [map_mul, bankProduct_star S α hα ℓ z, clockCompletion_star hβ ℓ₀ z]
  ring

/-- **The completed strand exchange (packaged form).**  There is a unimodular constant `ε'`
with `(E·γ)*(z̄) = ε'·(E·γ)(z)` for all `z`, where `E·γ = completedBank S α ℓ β ℓ₀` is the
completed finite bank and `ε' = (∏_{i ∈ S} (−ᾱ_i))·β̄²`.  This is the `E*(z̄) = ε·E(z)` strand
exchange applied to the completed object of `CompletedReflectionFiber`, with the exchange
constant carrying the extra completion-clock factor `β̄²`.  Finite `S`; unit clock faces.  The
`s ↦ 1-s` completed functional equation (`symTensorCompleted_FE`) is a distinct reflection and
is not claimed here. -/
theorem completedBank_exchange {ι : Type*} (S : Finset ι) (α : ι → ℂ)
    (hα : ∀ i ∈ S, ‖α i‖ = 1) (ℓ : ι → ℝ) (β : ℂ) (hβ : ‖β‖ = 1) (ℓ₀ : ℝ) :
    ∃ ε : ℂ, ‖ε‖ = 1 ∧ ∀ z : ℂ,
      (starRingEnd ℂ) (completedBank S α ℓ β ℓ₀ ((starRingEnd ℂ) z))
        = ε * completedBank S α ℓ β ℓ₀ z := by
  refine ⟨(∏ i ∈ S, (-(starRingEnd ℂ) (α i))) * ((starRingEnd ℂ) β) ^ 2, ?_, fun z => ?_⟩
  · rw [norm_mul, bankProduct_star_norm_one S α hα, one_mul, norm_pow, RCLike.norm_conj, hβ,
      one_pow]
  · exact completedBank_star S α hα ℓ β hβ ℓ₀ z

end CriticalLinePhasor.StrandExchange

#print axioms CriticalLinePhasor.StrandExchange.bankProduct_exchange
#print axioms CriticalLinePhasor.StrandExchange.completedBank_exchange
