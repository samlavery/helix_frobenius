import RequestProject.CarrierThetaDecay

/-!
# Strong functional equations for coefficient-assembled carrier theta functions

This module combines three independently compiled pieces:

* polynomial coefficient growth plus rapid kernel decay gives rapid theta decay;
* an exact theta reflection gives a `StrongFEPair` and hence entire, strip-bounded Mellin transforms;
* the initial-half-plane Mellin calculation identifies that entire transform with the specified
  Dirichlet readout times the completion factor.
-/

open Complex Set Filter Topology MeasureTheory Asymptotics

namespace CriticalLinePhasor.CarrierTheta

/-- A primal/dual pair of coefficient theta banks with an exact carrier reflection defines a strong
Riemann--Hecke pair. -/
noncomputable def coefficientThetaStrongFEPair
    (a aDual : ℕ → ℂ) (g gDual : ℝ → ℂ)
    (C A CDual ADual : ℝ)
    (hC : 0 ≤ C) (hCDual : 0 ≤ CDual)
    (ha : ∀ n : ℕ, ‖a n‖ ≤ C * (((n + 1 : ℕ) : ℝ) ^ A))
    (haDual : ∀ n : ℕ, ‖aDual n‖ ≤ CDual * (((n + 1 : ℕ) : ℝ) ^ ADual))
    (hg : ∀ q : ℝ, g =O[atTop] (fun x : ℝ => x ^ q))
    (hgDual : ∀ q : ℝ, gDual =O[atTop] (fun x : ℝ => x ^ q))
    (hf_int : LocallyIntegrableOn (theta a g) (Ioi 0))
    (hg_int : LocallyIntegrableOn (theta aDual gDual) (Ioi 0))
    (k : ℝ) (hk : 0 < k) (ε : ℂ) (hε : ε ≠ 0)
    (hfeq : ∀ x ∈ Ioi (0 : ℝ),
      theta a g (1 / x) = (ε * (x ^ k : ℝ)) • theta aDual gDual x) :
    StrongFEPair ℂ where
  toWeakFEPair := {
    f := theta a g
    g := theta aDual gDual
    k := k
    ε := ε
    f₀ := 0
    g₀ := 0
    hf_int := hf_int
    hg_int := hg_int
    hk := hk
    hε := hε
    h_feq := hfeq
    hf_top := fun r => by
      simpa using theta_rapid_of_polynomial_of_kernel_rapid a g C A hC ha hg r
    hg_top := fun r => by
      simpa using theta_rapid_of_polynomial_of_kernel_rapid
        aDual gDual CDual ADual hCDual haDual hgDual r
  }
  hf₀ := rfl
  hg₀ := rfl

/-- The full analytic payload of an exact reflected coefficient theta pair. -/
theorem coefficientTheta_twistedNiceness
    (a aDual : ℕ → ℂ) (g gDual : ℝ → ℂ)
    (C A CDual ADual : ℝ)
    (hC : 0 ≤ C) (hCDual : 0 ≤ CDual)
    (ha : ∀ n : ℕ, ‖a n‖ ≤ C * (((n + 1 : ℕ) : ℝ) ^ A))
    (haDual : ∀ n : ℕ, ‖aDual n‖ ≤ CDual * (((n + 1 : ℕ) : ℝ) ^ ADual))
    (hg : ∀ q : ℝ, g =O[atTop] (fun x : ℝ => x ^ q))
    (hgDual : ∀ q : ℝ, gDual =O[atTop] (fun x : ℝ => x ^ q))
    (hf_int : LocallyIntegrableOn (theta a g) (Ioi 0))
    (hg_int : LocallyIntegrableOn (theta aDual gDual) (Ioi 0))
    (k : ℝ) (hk : 0 < k) (ε : ℂ) (hε : ε ≠ 0)
    (hfeq : ∀ x ∈ Ioi (0 : ℝ),
      theta a g (1 / x) = (ε * (x ^ k : ℝ)) • theta aDual gDual x) :
    let P := coefficientThetaStrongFEPair a aDual g gDual C A CDual ADual hC hCDual
      ha haDual hg hgDual hf_int hg_int k hk ε hε hfeq
    Differentiable ℂ P.Λ ∧
    Differentiable ℂ P.symm.Λ ∧
    (∀ u v : ℝ, ∃ B : ℝ, ∀ s : ℂ,
      u ≤ s.re → s.re ≤ v → ‖P.Λ s‖ ≤ B) ∧
    (∀ u v : ℝ, ∃ B : ℝ, ∀ s : ℂ,
      u ≤ s.re → s.re ≤ v → ‖P.symm.Λ s‖ ≤ B) ∧
    (∀ s : ℂ, P.Λ (P.k - s) = P.ε • P.symm.Λ s) := by
  dsimp only
  let P := coefficientThetaStrongFEPair a aDual g gDual C A CDual ADual hC hCDual
    ha haDual hg hgDual hf_int hg_int k hk ε hε hfeq
  exact ⟨P.differentiable_Λ, P.symm.differentiable_Λ,
    fun u v => CriticalLinePhasor.CarrierMellinContinuation.strongFEPair_boundedOn_verticalStrip
      P u v,
    fun u v => CriticalLinePhasor.CarrierMellinContinuation.strongFEPair_boundedOn_verticalStrip
      P.symm u v,
    P.functional_equation⟩

/-- On the initial half-plane, the entire strong-FE transform is exactly the Dirichlet readout
times the Mellin transform of the completion kernel. -/
theorem coefficientTheta_initial_identification
    (a aDual : ℕ → ℂ) (g gDual : ℝ → ℂ)
    (C A CDual ADual : ℝ)
    (hC : 0 ≤ C) (hCDual : 0 ≤ CDual)
    (ha : ∀ n : ℕ, ‖a n‖ ≤ C * (((n + 1 : ℕ) : ℝ) ^ A))
    (haDual : ∀ n : ℕ, ‖aDual n‖ ≤ CDual * (((n + 1 : ℕ) : ℝ) ^ ADual))
    (hg : ∀ q : ℝ, g =O[atTop] (fun x : ℝ => x ^ q))
    (hgDual : ∀ q : ℝ, gDual =O[atTop] (fun x : ℝ => x ^ q))
    (hf_int : LocallyIntegrableOn (theta a g) (Ioi 0))
    (hg_int : LocallyIntegrableOn (theta aDual gDual) (Ioi 0))
    (k : ℝ) (hk : 0 < k) (ε : ℂ) (hε : ε ≠ 0)
    (hfeq : ∀ x ∈ Ioi (0 : ℝ),
      theta a g (1 / x) = (ε * (x ^ k : ℝ)) • theta aDual gDual x)
    (s : ℂ) (hgm : MellinConvergent g s) (hs : A + 1 < s.re) :
    let P := coefficientThetaStrongFEPair a aDual g gDual C A CDual ADual hC hCDual
      ha haDual hg hgDual hf_int hg_int k hk ε hε hfeq
    P.Λ s = dirichlet a s * mellin g s := by
  dsimp only
  change mellin (theta a g) s = dirichlet a s * mellin g s
  exact (theta_hasMellin_of_polynomial a g s C A hgm ha hs).2

end CriticalLinePhasor.CarrierTheta

#print axioms CriticalLinePhasor.CarrierTheta.coefficientThetaStrongFEPair
#print axioms CriticalLinePhasor.CarrierTheta.coefficientTheta_twistedNiceness
#print axioms CriticalLinePhasor.CarrierTheta.coefficientTheta_initial_identification
