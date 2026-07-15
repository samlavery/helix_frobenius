import RequestProject.GlobalHelixClebschGordanBank

/-!
# Clebsch--Gordan passage from finite Euler banks to global limits

The finite-place identity is exact at every stage.  Continuity of multiplication transports it to
any convergent exhaustion of the places.  When the lower global factor is nonzero, the top
symmetric-power twist is consequently the quotient of the tensor step by the lower block.
-/

open Complex Filter Topology
open scoped BigOperators

namespace CriticalLinePhasor.GlobalHelix

/-- Finite Euler approximant for `Sym^r × τ`. -/
noncomputable def symTwistEulerApprox
    {V κ : Type*} [Fintype κ] [DecidableEq V]
    (S : Finset V) (r : ℕ)
    (α : V → ℂ) (hα : ∀ v, ‖α v‖ = 1)
    (Wτ : V → FiniteWeightFiber κ) (q : V → ℝ) (s : ℂ) : ℂ :=
  ∏ v ∈ S,
    (FiniteWeightFiber.tensorFiber
      (FiniteWeightFiber.symFiber r (α v) (hα v)) (Wτ v)).localFactor (q v) s

/-- Finite Euler approximant for `(Sym^1 ⊗ Sym^(r-1)) × τ`. -/
noncomputable def tensorStepTwistEulerApprox
    {V κ : Type*} [Fintype κ] [DecidableEq V]
    (S : Finset V) (r : ℕ)
    (α : V → ℂ) (hα : ∀ v, ‖α v‖ = 1)
    (Wτ : V → FiniteWeightFiber κ) (q : V → ℝ) (s : ℂ) : ℂ :=
  ∏ v ∈ S,
    (FiniteWeightFiber.tensorFiber
      (FiniteWeightFiber.tensorFiber
        (FiniteWeightFiber.symFiber 1 (α v) (hα v))
        (FiniteWeightFiber.symFiber (r - 1) (α v) (hα v))) (Wτ v)).localFactor (q v) s

/-- Stagewise global-bank Clebsch--Gordan identity. -/
theorem tensorStepTwistEulerApprox_eq_mul
    {V κ : Type*} [Fintype κ] [DecidableEq V]
    (S : Finset V) {r : ℕ} (hr : 2 ≤ r)
    (α : V → ℂ) (hα : ∀ v, ‖α v‖ = 1)
    (Wτ : V → FiniteWeightFiber κ) (q : V → ℝ) (s : ℂ) :
    tensorStepTwistEulerApprox S r α hα Wτ q s =
      symTwistEulerApprox S r α hα Wτ q s *
        symTwistEulerApprox S (r - 2) α hα Wτ q s := by
  exact finiteTensorSymTwistEulerProduct_eq_mul S hr α hα Wτ q s

/-- Passing a cofinal sequence of exact finite-bank identities to convergent Euler limits. -/
theorem tensorStepTwistEulerLimit_eq_mul
    {V κ : Type*} [Fintype κ] [DecidableEq V]
    (S : ℕ → Finset V) {r : ℕ} (hr : 2 ≤ r)
    (α : V → ℂ) (hα : ∀ v, ‖α v‖ = 1)
    (Wτ : V → FiniteWeightFiber κ) (q : V → ℝ) (s : ℂ)
    (Lstep Ltop Llower : ℂ)
    (hstep : Tendsto
      (fun N => tensorStepTwistEulerApprox (S N) r α hα Wτ q s)
      atTop (𝓝 Lstep))
    (htop : Tendsto
      (fun N => symTwistEulerApprox (S N) r α hα Wτ q s)
      atTop (𝓝 Ltop))
    (hlower : Tendsto
      (fun N => symTwistEulerApprox (S N) (r - 2) α hα Wτ q s)
      atTop (𝓝 Llower)) :
    Lstep = Ltop * Llower := by
  have hmul : Tendsto
      (fun N => symTwistEulerApprox (S N) r α hα Wτ q s *
        symTwistEulerApprox (S N) (r - 2) α hα Wτ q s)
      atTop (𝓝 (Ltop * Llower)) := htop.mul hlower
  have heq : (fun N => tensorStepTwistEulerApprox (S N) r α hα Wτ q s) =
      fun N => symTwistEulerApprox (S N) r α hα Wτ q s *
        symTwistEulerApprox (S N) (r - 2) α hα Wτ q s := by
    funext N
    exact tensorStepTwistEulerApprox_eq_mul (S N) hr α hα Wτ q s
  rw [heq] at hstep
  exact tendsto_nhds_unique hstep hmul

/-- Isolation of the global top block after the lower limit is known nonzero. -/
theorem symTwistEulerLimit_eq_div
    {V κ : Type*} [Fintype κ] [DecidableEq V]
    (S : ℕ → Finset V) {r : ℕ} (hr : 2 ≤ r)
    (α : V → ℂ) (hα : ∀ v, ‖α v‖ = 1)
    (Wτ : V → FiniteWeightFiber κ) (q : V → ℝ) (s : ℂ)
    (Lstep Ltop Llower : ℂ)
    (hstep : Tendsto
      (fun N => tensorStepTwistEulerApprox (S N) r α hα Wτ q s)
      atTop (𝓝 Lstep))
    (htop : Tendsto
      (fun N => symTwistEulerApprox (S N) r α hα Wτ q s)
      atTop (𝓝 Ltop))
    (hlower : Tendsto
      (fun N => symTwistEulerApprox (S N) (r - 2) α hα Wτ q s)
      atTop (𝓝 Llower))
    (hLlower : Llower ≠ 0) :
    Ltop = Lstep / Llower := by
  apply (eq_div_iff hLlower).2
  exact (tensorStepTwistEulerLimit_eq_mul S hr α hα Wτ q s
    Lstep Ltop Llower hstep htop hlower).symm

end CriticalLinePhasor.GlobalHelix

#print axioms CriticalLinePhasor.GlobalHelix.tensorStepTwistEulerApprox_eq_mul
#print axioms CriticalLinePhasor.GlobalHelix.tensorStepTwistEulerLimit_eq_mul
#print axioms CriticalLinePhasor.GlobalHelix.symTwistEulerLimit_eq_div
